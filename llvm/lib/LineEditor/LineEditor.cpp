//===-- LineEditor.cpp - line editor --------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/LineEditor/LineEditor.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Config/config.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cassert>
#include <cerrno>
#include <clocale>
#include <csignal>
#include <cstdio>
#if !defined(_WIN32)
#include <sys/ioctl.h>
#include <unistd.h>
#endif
#ifdef HAVE_LIBEDIT
#include <histedit.h>
constexpr int DefaultHistorySize = 800;
#endif

using namespace llvm;

namespace {
static volatile sig_atomic_t GotSigInt = 0;
#if !defined(_WIN32)
static void LineEditorSigIntHandler(int) { GotSigInt = 1; }
static void installSigIntHandler() {
  struct sigaction SA = {};
  SA.sa_handler = LineEditorSigIntHandler;
  sigemptyset(&SA.sa_mask);
  SA.sa_flags = 0; // Do not SA_RESTART so read() returns EINTR
  ::sigaction(SIGINT, &SA, nullptr);
}
#else
static void installSigIntHandler() {}
#endif
} // namespace

std::string LineEditor::getDefaultHistoryPath(StringRef ProgName) {
  SmallString<32> Path;
  if (sys::path::home_directory(Path)) {
    sys::path::append(Path, "." + ProgName + "-history");
    return std::string(Path);
  }
  return std::string();
}

LineEditor::CompleterConcept::~CompleterConcept() = default;
LineEditor::ListCompleterConcept::~ListCompleterConcept() = default;

std::string LineEditor::ListCompleterConcept::getCommonPrefix(
    const std::vector<Completion> &Comps) {
  assert(!Comps.empty());

  std::string CommonPrefix = Comps[0].TypedText;
  for (const Completion &C : llvm::drop_begin(Comps)) {
    size_t Len = std::min(CommonPrefix.size(), C.TypedText.size());
    size_t CommonLen = 0;
    for (; CommonLen != Len; ++CommonLen) {
      if (CommonPrefix[CommonLen] != C.TypedText[CommonLen])
        break;
    }
    CommonPrefix.resize(CommonLen);
  }
  return CommonPrefix;
}

LineEditor::CompletionAction
LineEditor::ListCompleterConcept::complete(StringRef Buffer, size_t Pos) const {
  CompletionAction Action;
  std::vector<Completion> Comps = getCompletions(Buffer, Pos);
  if (Comps.empty()) {
    Action.Kind = CompletionAction::AK_ShowCompletions;
    return Action;
  }

  std::string CommonPrefix = getCommonPrefix(Comps);

  // If the common prefix is non-empty we can simply insert it. If there is a
  // single completion, this will insert the full completion. If there is more
  // than one, this might be enough information to jog the user's memory but if
  // not the user can also hit tab again to see the completions because the
  // common prefix will then be empty.
  if (CommonPrefix.empty()) {
    Action.Kind = CompletionAction::AK_ShowCompletions;
    for (const Completion &Comp : Comps)
      Action.Completions.push_back(Comp.DisplayText);
  } else {
    Action.Kind = CompletionAction::AK_Insert;
    Action.Text = CommonPrefix;
  }

  return Action;
}

LineEditor::CompletionAction LineEditor::getCompletionAction(StringRef Buffer,
                                                             size_t Pos) const {
  if (!Completer) {
    CompletionAction Action;
    Action.Kind = CompletionAction::AK_ShowCompletions;
    return Action;
  }

  return Completer->complete(Buffer, Pos);
}

#ifdef HAVE_LIBEDIT

// libedit-based implementation.

struct LineEditor::InternalData {
  LineEditor *LE;

  History *Hist;
  EditLine *EL;

  unsigned PrevCount;
  std::string ContinuationOutput;
  // The hint as libedit's right prompt shows it, dim.
  std::string RPrompt;

  FILE *Out;
};

namespace {

const char *ElGetPromptFn(EditLine *EL) {
  LineEditor::InternalData *Data;
  if (el_get(EL, EL_CLIENTDATA, &Data) == 0)
    return Data->LE->getPrompt().c_str();
  return "> ";
}

const char *ElGetRPromptFn(EditLine *EL) {
  LineEditor::InternalData *Data;
  if (el_get(EL, EL_CLIENTDATA, &Data) == 0)
    return Data->RPrompt.c_str();
  return "";
}

// The hint for the line as it is now, as the right prompt.
void refreshHint(EditLine *EL, LineEditor::InternalData *Data) {
  const LineInfo *LI = ::el_line(EL);
  Data->LE->updateHint(StringRef(LI->buffer, LI->lastchar - LI->buffer),
                       LI->cursor - LI->buffer);
  const std::string &Hint = Data->LE->getHint();
  Data->RPrompt = Hint.empty() ? std::string()
                               : "\001\033[90m\001 " + Hint + "\001\033[0m\001";
}

// A character typed: inserted, then the hint made again.
unsigned char ElHintInsertFn(EditLine *EL, int Ch) {
  LineEditor::InternalData *Data;
  if (el_get(EL, EL_CLIENTDATA, &Data) != 0)
    return CC_ERROR;
  char Text[2] = {static_cast<char>(Ch), '\0'};
  if (::el_insertstr(EL, Text) == -1)
    return CC_ERROR;
  refreshHint(EL, Data);
  return CC_REFRESH;
}

// Backspace: the character before the cursor taken out, then the hint.
unsigned char ElHintDeleteFn(EditLine *EL, int) {
  LineEditor::InternalData *Data;
  if (el_get(EL, EL_CLIENTDATA, &Data) != 0)
    return CC_ERROR;
  const LineInfo *LI = ::el_line(EL);
  if (LI->cursor == LI->buffer)
    return CC_REFRESH_BEEP;
  ::el_deletestr(EL, 1);
  refreshHint(EL, Data);
  return CC_REFRESH;
}

// Enter: the hint taken off the line, then libedit's own newline. The line
// is drawn again without the hint (CC_REFRESH), and ed-newline -- bound to
// ^X^J for this alone, its key pushed back -- enters it as libedit always
// does: drawing it ourselves left the line's colours to the hint's (the line
// dim) and the hint itself behind.
unsigned char ElHintEnterFn(EditLine *EL, int) {
  LineEditor::InternalData *Data;
  if (el_get(EL, EL_CLIENTDATA, &Data) != 0)
    return CC_ERROR;
  Data->LE->clearHint();
  Data->RPrompt.clear();
  ::el_push(EL, const_cast<char *>("\030\012"));
  return CC_REFRESH;
}

// Handles tab completion.
//
// This function is really horrible. But since the alternative is to get into
// the line editor business, here we are.
unsigned char ElCompletionFn(EditLine *EL, int ch) {
  LineEditor::InternalData *Data;
  if (el_get(EL, EL_CLIENTDATA, &Data) == 0) {
    if (!Data->ContinuationOutput.empty()) {
      // This is the continuation of the AK_ShowCompletions branch below.
      FILE *Out = Data->Out;

      // Print the required output (see below).
      ::fwrite(Data->ContinuationOutput.c_str(),
               Data->ContinuationOutput.size(), 1, Out);

      // Push a sequence of Ctrl-B characters to move the cursor back to its
      // original position.
      std::string Prevs(Data->PrevCount, '\02');
      ::el_push(EL, const_cast<char *>(Prevs.c_str()));

      Data->ContinuationOutput.clear();

      return CC_REFRESH;
    }

    const LineInfo *LI = ::el_line(EL);
    LineEditor::CompletionAction Action = Data->LE->getCompletionAction(
        StringRef(LI->buffer, LI->lastchar - LI->buffer),
        LI->cursor - LI->buffer);
    switch (Action.Kind) {
    case LineEditor::CompletionAction::AK_Insert:
      ::el_insertstr(EL, Action.Text.c_str());
      return CC_REFRESH;

    case LineEditor::CompletionAction::AK_ShowCompletions:
      if (Action.Completions.empty()) {
        return CC_REFRESH_BEEP;
      } else {
        // Push a Ctrl-E and a tab. The Ctrl-E causes libedit to move the cursor
        // to the end of the line, so that when we emit a newline we will be on
        // a new blank line. The tab causes libedit to call this function again
        // after moving the cursor. There doesn't seem to be anything we can do
        // from here to cause libedit to move the cursor immediately. This will
        // break horribly if the user has rebound their keys, so for now we do
        // not permit user rebinding.
        ::el_push(EL, const_cast<char *>("\05\t"));

        // This assembles the output for the continuation block above.
        raw_string_ostream OS(Data->ContinuationOutput);

        // Move cursor to a blank line.
        OS << "\n";

        auto visualWidth = [](StringRef S) -> size_t {
          size_t W = 0;
          for (size_t I = 0; I < S.size();) {
            unsigned char C = static_cast<unsigned char>(S[I]);
            if (C == '\001') {
              ++I;
              continue;
            }
            if (C == '\033' && I + 1 < S.size() && S[I + 1] == '[') {
              I += 2;
              while (I < S.size() &&
                     (static_cast<unsigned char>(S[I]) < 0x40 ||
                      static_cast<unsigned char>(S[I]) > 0x7E))
                ++I;
              if (I < S.size())
                ++I;
              continue;
            }
            if ((C & 0xC0) != 0x80)
              ++W;
            ++I;
          }
          return W;
        };

        size_t TermWidth = 80;
#if !defined(_WIN32)
        struct winsize WS;
        if (::ioctl(fileno(Data->Out), TIOCGWINSZ, &WS) == 0 && WS.ws_col > 20)
          TermWidth = WS.ws_col;
#endif
        bool HasMultiline = false;
        size_t MaxW = 0;
        std::vector<size_t> Widths;
        Widths.reserve(Action.Completions.size());
        for (const std::string &C : Action.Completions) {
          if (C.find('\n') != std::string::npos)
            HasMultiline = true;
          size_t W = visualWidth(C);
          Widths.push_back(W);
          if (W > MaxW)
            MaxW = W;
        }
        size_t ColWidth = MaxW + 3;
        size_t NumCols =
            HasMultiline
                ? 1
                : std::max<size_t>(1, TermWidth / std::max<size_t>(1, ColWidth));
        size_t NumItems = Action.Completions.size();
        size_t NumRows = (NumItems + NumCols - 1) / NumCols;

        for (size_t R = 0; R < NumRows; ++R) {
          for (size_t C = 0; C < NumCols; ++C) {
            size_t Idx = R + C * NumRows;
            if (Idx >= NumItems)
              break;
            OS << Action.Completions[Idx];
            if (C + 1 < NumCols && Idx + NumRows < NumItems) {
              size_t Pad = ColWidth > Widths[Idx] ? (ColWidth - Widths[Idx]) : 2;
              OS.indent(Pad);
            }
          }
          OS << "\n";
        }

        // Fool libedit into thinking nothing has changed. Reprint its prompt
        // (stripping \001 markers) and the user input.
        for (char Ch : Data->LE->getPrompt())
          if (Ch != '\001')
            OS << Ch;
        OS << StringRef(LI->buffer, LI->lastchar - LI->buffer);

        // This is the number of characters we need to tell libedit to go back:
        // the distance between end of line and the original cursor position.
        Data->PrevCount = LI->lastchar - LI->cursor;

        return CC_REFRESH;
      }
    }
  }
  return CC_ERROR;
}

} // end anonymous namespace

LineEditor::LineEditor(StringRef ProgName, StringRef HistoryPath, FILE *In,
                       FILE *Out, FILE *Err)
    : Prompt((ProgName + "> ").str()), HistoryPath(std::string(HistoryPath)),
      Data(new InternalData) {
  if (HistoryPath.empty())
    this->HistoryPath = getDefaultHistoryPath(ProgName);

  Data->LE = this;
  Data->Out = Out;

  if (!std::setlocale(LC_ALL, ""))
    std::setlocale(LC_ALL, "C.UTF-8");

  installSigIntHandler();

  Data->Hist = ::history_init();
  assert(Data->Hist);

  Data->EL = ::el_init(ProgName.str().c_str(), In, Out, Err);
  assert(Data->EL);

  ::el_set(Data->EL, EL_PROMPT_ESC, ElGetPromptFn, '\001');
  ::el_set(Data->EL, EL_EDITOR, "emacs");
  ::el_set(Data->EL, EL_SIGNAL, 0);
  ::el_set(Data->EL, EL_HIST, history, Data->Hist);
  ::el_set(Data->EL, EL_ADDFN, "tab_complete", "Tab completion function",
           ElCompletionFn);
  ::el_set(Data->EL, EL_BIND, "\t", "tab_complete", NULL);
  // The hint (setHinter): at the right of the line, made again as it is
  // edited -- every printable character typed, Backspace -- and taken off
  // as it is entered.
  ::el_set(Data->EL, EL_RPROMPT_ESC, ElGetRPromptFn, '\001');
  ::el_set(Data->EL, EL_ADDFN, "hint_insert", "Insert, then hint", ElHintInsertFn);
  ::el_set(Data->EL, EL_ADDFN, "hint_delete", "Delete back, then hint", ElHintDeleteFn);
  ::el_set(Data->EL, EL_ADDFN, "hint_enter", "Enter without the hint", ElHintEnterFn);
  for (int Ch = 0x20; Ch < 0x7f; ++Ch) {
    // Each key written as an octal escape: libedit's bind reads a key that
    // starts with '-' as one of its switches, and '^', '\\' as escapes.
    char Key[8];
    std::snprintf(Key, sizeof Key, "\\%03o", Ch);
    ::el_set(Data->EL, EL_BIND, Key, "hint_insert", NULL);
  }
  ::el_set(Data->EL, EL_BIND, "^?", "hint_delete", NULL);
  ::el_set(Data->EL, EL_BIND, "^H", "hint_delete", NULL);
  ::el_set(Data->EL, EL_BIND, "^M", "hint_enter", NULL);
  ::el_set(Data->EL, EL_BIND, "^J", "hint_enter", NULL);
  ::el_set(Data->EL, EL_BIND, "^X^J", "ed-newline", NULL);
  ::el_set(Data->EL, EL_BIND, "^r", "em-inc-search-prev",
           NULL); // Cycle through backwards search, entering string
  ::el_set(Data->EL, EL_BIND, "^w", "ed-delete-prev-word",
           NULL); // Delete previous word, behave like bash does.
  ::el_set(Data->EL, EL_BIND, "\033[3~", "ed-delete-next-char",
           NULL); // Fix the delete key.
  ::el_set(Data->EL, EL_CLIENTDATA, Data.get());

  setHistorySize(DefaultHistorySize);
  HistEvent HE;
  ::history(Data->Hist, &HE, H_SETUNIQUE, 1);
  loadHistory();
}

LineEditor::~LineEditor() {
  saveHistory();

  ::history_end(Data->Hist);
  ::el_end(Data->EL);
  ::fwrite("\n", 1, 1, Data->Out);
}

void LineEditor::saveHistory() {
  if (!HistoryPath.empty()) {
    HistEvent HE;
    ::history(Data->Hist, &HE, H_SAVE, HistoryPath.c_str());
  }
}

void LineEditor::loadHistory() {
  if (!HistoryPath.empty()) {
    HistEvent HE;
    ::history(Data->Hist, &HE, H_LOAD, HistoryPath.c_str());
  }
}

void LineEditor::setHistorySize(int size) {
  HistEvent HE;
  ::history(Data->Hist, &HE, H_SETSIZE, size);
}

std::optional<std::string> LineEditor::readLine() const {
  installSigIntHandler();
  GotSigInt = 0;
  errno = 0;
  clearHint();
  Data->RPrompt.clear();

  // Call el_gets to prompt the user and read the user's input.
  int LineLen = 0;
  const char *Line = ::el_gets(Data->EL, &LineLen);

  if (GotSigInt || (!Line && errno == EINTR) || LineLen < 0) {
    GotSigInt = 0;
    ::el_reset(Data->EL);
    ::fwrite("^C\n", 1, 3, Data->Out);
    ::fflush(Data->Out);
    return std::string("\x03");
  }

  // Either of these may mean end-of-file.
  if (!Line || LineLen == 0)
    return std::nullopt;

  // Strip any newlines off the end of the string.
  while (LineLen > 0 &&
         (Line[LineLen - 1] == '\n' || Line[LineLen - 1] == '\r'))
    --LineLen;

  HistEvent HE;
  if (LineLen > 0)
    ::history(Data->Hist, &HE, H_ENTER, Line);

  return std::string(Line, LineLen);
}

#else // HAVE_LIBEDIT

// Simple fgets-based implementation.

struct LineEditor::InternalData {
  FILE *In;
  FILE *Out;
};

LineEditor::LineEditor(StringRef ProgName, StringRef HistoryPath, FILE *In,
                       FILE *Out, FILE *Err)
    : Prompt((ProgName + "> ").str()), Data(new InternalData) {
  Data->In = In;
  Data->Out = Out;
}

LineEditor::~LineEditor() {
  ::fwrite("\n", 1, 1, Data->Out);
}

void LineEditor::saveHistory() {}
void LineEditor::loadHistory() {}
void LineEditor::setHistorySize(int size) {}

std::optional<std::string> LineEditor::readLine() const {
  std::string CleanPrompt;
  CleanPrompt.reserve(Prompt.size());
  for (char C : Prompt)
    if (C != '\001')
      CleanPrompt.push_back(C);
  ::fprintf(Data->Out, "%s", CleanPrompt.c_str());

  std::string Line;
  do {
    char Buf[64];
    char *Res = ::fgets(Buf, sizeof(Buf), Data->In);
    if (!Res) {
      if (Line.empty())
        return std::nullopt;
      else
        return Line;
    }
    Line.append(Buf);
  } while (Line.empty() ||
           (Line[Line.size() - 1] != '\n' && Line[Line.size() - 1] != '\r'));

  while (!Line.empty() &&
         (Line[Line.size() - 1] == '\n' || Line[Line.size() - 1] == '\r'))
    Line.resize(Line.size() - 1);

  return Line;
}

#endif // HAVE_LIBEDIT
