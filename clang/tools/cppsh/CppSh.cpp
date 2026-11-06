//===--- tools/cppsh/CppSh.cpp - cppsh - the C++26 Shell ------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticFrontend.h"
#include "clang/Basic/Version.h"
#include "clang/Config/config.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Interpreter/CodeCompletion.h"
#include "clang/Interpreter/Interpreter.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Sema.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/LineEditor/LineEditor.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/TargetParser/Triple.h"

#include <algorithm>
#include <cctype>
#include <clocale>
#include <cstdlib>
#include <map>
#include <optional>
#include <regex>
#include <set>
#include <string>
#include <vector>

#if !defined(_WIN32)
#include <poll.h>
#include <pwd.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

#if LLVM_ADDRESS_SANITIZER_BUILD || LLVM_HWADDRESS_SANITIZER_BUILD
#include <sanitizer/lsan_interface.h>
LLVM_ATTRIBUTE_USED int __lsan_is_turned_off() { return 1; }
#endif

#define DEBUG_TYPE "cppsh"

static llvm::cl::list<std::string>
    ClangArgs("Xcc",
              llvm::cl::desc("Argument to pass to the CompilerInvocation"),
              llvm::cl::CommaSeparated);
static llvm::cl::opt<std::string>
    CommandString("c", llvm::cl::desc("Execute command string and exit"),
                  llvm::cl::value_desc("command"), llvm::cl::init(""));
static llvm::cl::opt<bool>
    NoStdSh("no-std-sh", llvm::cl::desc("Do not auto-import std.sh at startup"),
            llvm::cl::init(false));
static llvm::cl::list<std::string> OptInputs(llvm::cl::Positional,
                                             llvm::cl::desc("[script or code]"));

static const char *const CppShRuntimePrelude = "import std.sh;";

static std::string getUsername() {
  if (const char *U = std::getenv("USER"))
    if (*U)
      return U;
  if (const char *U = std::getenv("LOGNAME"))
    if (*U)
      return U;
#if !defined(_WIN32)
  if (struct passwd *PW = ::getpwuid(::geteuid()))
    if (PW->pw_name && *PW->pw_name)
      return PW->pw_name;
#endif
  return "user";
}

static std::string getDisplayCwd() {
  llvm::SmallString<256> Cwd;
  if (llvm::sys::fs::current_path(Cwd))
    return "?";
  llvm::StringRef CwdRef(Cwd);
  if (const char *Home = std::getenv("HOME")) {
    llvm::StringRef HomeRef(Home);
    if (!HomeRef.empty() && CwdRef.starts_with(HomeRef)) {
      if (CwdRef.size() == HomeRef.size())
        return "~";
      if (CwdRef[HomeRef.size()] == '/')
        return ("~" + CwdRef.substr(HomeRef.size())).str();
    }
  }
  return Cwd.str().str();
}

static std::string buildBashPrompt(bool LastFailed) {
  std::string User = getUsername();
  std::string Path = getDisplayCwd();
  bool IsRoot = false;
#if !defined(_WIN32)
  IsRoot = (::geteuid() == 0);
#endif
  const char *Dollar = IsRoot ? "#" : "$";

  const char *GreenBold = "\001\033[1;32m\001";
  const char *BlueBold = "\001\033[1;34m\001";
  const char *RedBold = "\001\033[1;31m\001";
  const char *Reset = "\001\033[0m\001";

  std::string P;
  P += GreenBold + User + Reset + " ";
  P += BlueBold + Path + Reset + " ";
  if (LastFailed)
    P += std::string(RedBold) + Dollar + Reset + " ";
  else
    P += std::string(Dollar) + " ";
  return P;
}

// The top-level statements of a piece of code, in order: split at each `;`
// outside brackets, string and character literals and comments (a `'`
// right after a letter or digit -- a digit separator, a `T'` -- opens
// nothing).
static std::vector<std::string> splitStatements(llvm::StringRef Code) {
  std::vector<std::string> Out;
  int Depth = 0;
  size_t Start = 0;
  for (size_t I = 0; I < Code.size(); ++I) {
    char C = Code[I];
    if (C == '"' ||
        (C == '\'' && !(I > 0 && std::isalnum(static_cast<unsigned char>(Code[I - 1]))))) {
      for (++I; I < Code.size() && Code[I] != C; ++I)
        if (Code[I] == '\\')
          ++I;
      continue;
    }
    if (C == '/' && I + 1 < Code.size() && Code[I + 1] == '/') {
      while (I < Code.size() && Code[I] != '\n')
        ++I;
      continue;
    }
    if (C == '/' && I + 1 < Code.size() && Code[I + 1] == '*') {
      size_t End = Code.find("*/", I + 2);
      I = End == llvm::StringRef::npos ? Code.size() : End + 1;
      continue;
    }
    if (C == '(' || C == '[' || C == '{')
      ++Depth;
    else if ((C == ')' || C == ']' || C == '}') && Depth > 0)
      --Depth;
    else if (C == ';' && Depth == 0) {
      Out.push_back(Code.substr(Start, I + 1 - Start).str());
      Start = I + 1;
    }
  }
  if (!Code.substr(Start).trim().empty())
    Out.push_back(Code.substr(Start).str());
  return Out;
}

// Code run a statement at a time: each compiled once the one before it has
// run, so that what it reads -- a variable std::cin filled the statement
// before -- is a value as it is compiled (the value specialization reads a
// run statement's variables from memory). The first failure stops the rest.
// The run variables a statement names that are not plain data -- a
// std::string, a container -- snapshotted before it is compiled
// (std::sh::__cppsh_snapshot), so that the value specialization of its
// calls rebuilds them as they are now. Plain data needs none: it is read
// from memory. Names after `.` or `->` are members, not variables; string
// and character literals are skipped.
static void snapshotNamed(clang::Interpreter &Interp, llvm::StringRef Stmt) {
  clang::Sema &S = Interp.getCompilerInstance()->getSema();
  clang::ASTContext &Ctx = S.getASTContext();
  auto identChar = [](char C) {
    unsigned char U = static_cast<unsigned char>(C);
    return std::isalnum(U) || C == '_' || U >= 0x80;
  };
  std::set<std::string> Names;
  for (size_t I = 0; I < Stmt.size();) {
    char C = Stmt[I];
    if (C == '"') {
      for (++I; I < Stmt.size() && Stmt[I] != '"'; ++I)
        if (Stmt[I] == '\\')
          ++I;
      ++I;
      continue;
    }
    if (!identChar(C)) {
      ++I;
      continue;
    }
    size_t J = I;
    while (J < Stmt.size() && identChar(Stmt[J]))
      ++J;
    bool Member = (I > 0 && Stmt[I - 1] == '.') ||
                  (I > 1 && Stmt[I - 1] == '>' && Stmt[I - 2] == '-');
    if (!Member && !std::isdigit(static_cast<unsigned char>(C)))
      Names.insert(Stmt.substr(I, J - I).str());
    I = J;
  }
  for (const std::string &Name : Names) {
    clang::LookupResult R(S, &Ctx.Idents.get(Name), clang::SourceLocation(),
                          clang::Sema::LookupOrdinaryName);
    R.suppressDiagnostics();
    if (!S.LookupQualifiedName(R, Ctx.getTranslationUnitDecl()))
      continue;
    auto *VD = R.getAsSingle<clang::VarDecl>();
    if (!VD || !VD->hasGlobalStorage() || VD->isInvalidDecl() ||
        VD->getType()->isDependentType() || VD->getType()->isReferenceType() ||
        VD->getType().isTriviallyCopyableType(Ctx))
      continue;
    if (llvm::Error Err =
            Interp.ParseAndExecute("std::sh::__cppsh_snapshot(" + Name + ");"))
      llvm::consumeError(std::move(Err));
  }
}

static llvm::Error runStatements(clang::Interpreter &Interp, llvm::StringRef Code) {
  for (const std::string &One : splitStatements(Code)) {
    snapshotNamed(Interp, One);
    if (llvm::Error Err = Interp.ParseAndExecute(One))
      return Err;
  }
  return llvm::Error::success();
}

// The type of the expression being typed, for the line editor's hint: Sema's
// own, the value specialization's included (`ls {.files_only = true}`:
// ls_view<file_entry>). Nothing where it does not parse yet, where a
// statement was just ended, or for the shell's own commands.
//
// Worked out in a fork of the shell, never in the session itself: parsing
// changes Sema beyond what an undo takes back -- a class template
// instantiated, the friends it defines (`define<tag, 42>()` typed, then
// erased, left adl_function(declare<tag>{}) defined), the value
// specialization's functions. The child, a copy of the whole session, parses
// `using __cppsh_hint_t = decltype(<it>);`, writes the type to a pipe and
// ends; the session is as it was. A child slower than kHintMillis is ended,
// and no hint shown.
static constexpr int kHintMillis = 150;

// The expression at the cursor: from the cursor -- to the end of the word
// under it -- back to the nearest unmatched '(', '[' or '{', or a ',', ';' or
// assignment '=' at that depth: in `obj = ls {.all = true}`, the cursor after
// '}', `ls {.all = true}`; in `f(x, y.size())`, after `size()`, `y.size()`.
static llvm::StringRef expressionAt(llvm::StringRef Buffer, size_t Pos) {
  auto identChar = [](char C) {
    unsigned char U = static_cast<unsigned char>(C);
    return std::isalnum(U) || C == '_' || U >= 0x80;
  };
  size_t End = std::min(Pos, Buffer.size());
  while (End < Buffer.size() && identChar(Buffer[End]))
    ++End;
  int Depth = 0;
  size_t Start = 0;
  for (size_t I = End; I > 0; --I) {
    char C = Buffer[I - 1];
    if (C == '"' || C == '\'') {
      // A literal: skipped whole, back to its opening quote.
      size_t J = I - 1;
      while (J > 0 && !(Buffer[J - 1] == C && (J < 2 || Buffer[J - 2] != '\\')))
        --J;
      I = J > 0 ? J : 1;
      continue;
    }
    if (C == ')' || C == ']' || C == '}') {
      ++Depth;
    } else if (C == '(' || C == '[' || C == '{') {
      if (Depth == 0) {
        Start = I;
        break;
      }
      --Depth;
    } else if (Depth == 0 && (C == ',' || C == ';')) {
      Start = I;
      break;
    } else if (Depth == 0 && C == '=') {
      char Before = I >= 2 ? Buffer[I - 2] : ' ';
      char After = I < Buffer.size() ? Buffer[I] : ' ';
      if (After != '=' && Before != '=' && Before != '!' && Before != '<' &&
          Before != '>') {
        Start = I;
        break;
      }
    }
  }
  return Buffer.substr(Start, End - Start).trim();
}

static std::string typeHint(clang::Interpreter &Interp, llvm::StringRef Buffer,
                            size_t Pos) {
  llvm::StringRef Expr = expressionAt(Buffer, Pos);
  if (Expr.empty() || Expr.ends_with(";") || Expr == "exit" || Expr == "quit" ||
      Expr == "clear" || Expr == "cd" || Expr.starts_with("cd ") ||
      Expr.starts_with("%") || Expr.starts_with("#"))
    return {};
  // The same text, the same hint: a cursor moved forks nothing.
  static std::string LastText, LastHint;
  if (Expr == LastText)
    return LastHint;
  LastText = Expr.str();
  LastHint.clear();
#if defined(_WIN32)
  (void)Interp;
  return {};
#else
  int Fds[2];
  if (::pipe(Fds) != 0)
    return {};
  pid_t Child = ::fork();
  if (Child < 0) {
    ::close(Fds[0]);
    ::close(Fds[1]);
    return {};
  }
  if (Child == 0) {
    // The copy: its diagnostics nowhere, its result down the pipe, its end
    // without running anything the session's exit would (_exit).
    ::close(Fds[0]);
    clang::DiagnosticsEngine &Diags = Interp.getCompilerInstance()->getDiagnostics();
    Diags.setClient(new clang::IgnoringDiagConsumer(), /*ShouldOwnClient=*/true);
    std::string Hint;
    std::string Code = "using __cppsh_hint_t = decltype(" + Expr.str() + ");";
    if (llvm::Expected<clang::PartialTranslationUnit &> PTU = Interp.Parse(Code)) {
      for (clang::Decl *D : PTU->TUPart->decls())
        if (auto *Alias = llvm::dyn_cast<clang::TypeAliasDecl>(D))
          if (Alias->getIdentifier() && Alias->getName() == "__cppsh_hint_t") {
            clang::PrintingPolicy PP(Alias->getASTContext().getLangOpts());
            PP.SuppressScope = true;
            // What decltype(...) and a deduced auto stand for, not their
            // spelling: the alias's type is decltype(obj) itself, which
            // printed as just that. Typedef names under them kept
            // (std::string, not basic_string<char, ...>).
            clang::QualType T = Alias->getUnderlyingType();
            for (;;) {
              if (const auto *DT = T->getAs<clang::DecltypeType>()) {
                T = DT->getUnderlyingType();
                continue;
              }
              if (const auto *AT = T->getAs<clang::AutoType>(); AT && AT->isDeduced()) {
                T = AT->getDeducedType();
                continue;
              }
              break;
            }
            Hint = T.getAsString(PP);
          }
    } else {
      llvm::consumeError(PTU.takeError());
    }
    size_t Off = 0;
    while (Off < Hint.size()) {
      ssize_t N = ::write(Fds[1], Hint.data() + Off, Hint.size() - Off);
      if (N <= 0)
        break;
      Off += static_cast<size_t>(N);
    }
    ::_exit(0);
  }
  ::close(Fds[1]);
  std::string Hint;
  bool TimedOut = false;
  for (;;) {
    struct pollfd P = {Fds[0], POLLIN, 0};
    int Ready = ::poll(&P, 1, kHintMillis);
    if (Ready == 0) {
      TimedOut = true;
      break;
    }
    if (Ready < 0) {
      if (errno == EINTR)
        continue;
      break;
    }
    char Buf[512];
    ssize_t N = ::read(Fds[0], Buf, sizeof Buf);
    if (N < 0 && errno == EINTR)
      continue;
    if (N <= 0)
      break;
    Hint.append(Buf, static_cast<size_t>(N));
  }
  ::close(Fds[0]);
  if (TimedOut) {
    ::kill(Child, SIGKILL);
    Hint.clear();
  }
  while (::waitpid(Child, nullptr, 0) < 0 && errno == EINTR) {
  }
  // A symbol -- a word nothing named (`dir` in `ls dir`) -- has no type to
  // speak of: no hint.
  if (llvm::StringRef(Hint).starts_with("sym<") || llvm::StringRef(Hint).starts_with("std::sh::sym<") ||
      llvm::StringRef(Hint).starts_with("const sym<"))
    Hint.clear();
  // Names as the shell's user writes them: without std::sh:: and std::.
  for (llvm::StringRef Scope : {"std::sh::", "std::ranges::", "std::"}) {
    for (size_t At; (At = Hint.find(Scope.str())) != std::string::npos;)
      Hint.erase(At, Scope.size());
  }
  LastHint = Hint;
  return Hint;
#endif
}

static llvm::Error runFileOrCode(clang::Interpreter &Interp,
                                 llvm::StringRef Input,
                                 bool ForceFile = false) {
  llvm::StringRef Trimmed = Input.trim();
  bool IsFile = ForceFile ||
                (!Trimmed.empty() && !Trimmed.contains('\n') &&
                 !Trimmed.contains(';') && llvm::sys::fs::exists(Trimmed) &&
                 !llvm::sys::fs::is_directory(Trimmed));
  if (!IsFile)
    return runStatements(Interp, Input);

  auto MBOrErr = llvm::MemoryBuffer::getFile(Trimmed);
  if (!MBOrErr)
    return llvm::createStringError(MBOrErr.getError(),
                                   "failed to read script file '%s'",
                                   Trimmed.str().c_str());
  llvm::StringRef Content = (*MBOrErr)->getBuffer();
  if (Content.starts_with("#!")) {
    size_t NL = Content.find('\n');
    Content = (NL == llvm::StringRef::npos) ? "" : Content.drop_front(NL + 1);
  }
  return runStatements(Interp, Content);
}

static void LLVMErrorHandler(void *UserData, const char *Message,
                             bool GenCrashDiag) {
  auto &Diags = *static_cast<clang::DiagnosticsEngine *>(UserData);
  Diags.Report(clang::diag::err_fe_error_backend) << Message;
  llvm::sys::RunInterruptHandlers();
  exit(GenCrashDiag ? 70 : 1);
}

struct ReplListCompleter {
  clang::IncrementalCompilerBuilder &CB;
  clang::Interpreter &MainInterp;
  ReplListCompleter(clang::IncrementalCompilerBuilder &CB,
                    clang::Interpreter &Interp)
      : CB(CB), MainInterp(Interp) {}

  static bool isIdentChar(char C) {
    unsigned char UC = static_cast<unsigned char>(C);
    return std::isalnum(UC) || C == '_' || UC >= 0x80;
  }

  static void lookupDeclsByName(clang::Sema &S, llvm::StringRef Name,
                                llvm::SmallVectorImpl<clang::NamedDecl *> &Out) {
    clang::ASTContext &Ctx = S.getASTContext();
    clang::IdentifierInfo *II = &Ctx.Idents.get(Name);
    auto collectFromCtx = [&](clang::DeclContext *DC) {
      if (!DC)
        return;
      clang::LookupResult R(S, II, clang::SourceLocation(),
                            clang::Sema::LookupOrdinaryName);
      R.suppressDiagnostics();
      if (S.LookupQualifiedName(R, DC))
        for (clang::NamedDecl *ND : R)
          Out.push_back(ND->getUnderlyingDecl());
    };
    collectFromCtx(Ctx.getTranslationUnitDecl());
    clang::LookupResult StdR(S, &Ctx.Idents.get("std"), clang::SourceLocation(),
                             clang::Sema::LookupNamespaceName);
    StdR.suppressDiagnostics();
    if (S.LookupQualifiedName(StdR, Ctx.getTranslationUnitDecl())) {
      for (clang::NamedDecl *StdND : StdR) {
        if (auto *StdNS = llvm::dyn_cast<clang::NamespaceDecl>(StdND)) {
          collectFromCtx(StdNS);
          for (llvm::StringRef SubName : {"sh", "ranges"}) {
            clang::LookupResult SubR(S, &Ctx.Idents.get(SubName),
                                     clang::SourceLocation(),
                                     clang::Sema::LookupNamespaceName);
            SubR.suppressDiagnostics();
            if (S.LookupQualifiedName(SubR, StdNS)) {
              for (clang::NamedDecl *SubND : SubR) {
                if (auto *SubNS = llvm::dyn_cast<clang::NamespaceDecl>(SubND)) {
                  collectFromCtx(SubNS);
                  if (SubName == "ranges") {
                    clang::LookupResult ViewsR(S, &Ctx.Idents.get("views"),
                                               clang::SourceLocation(),
                                               clang::Sema::LookupNamespaceName);
                    ViewsR.suppressDiagnostics();
                    if (S.LookupQualifiedName(ViewsR, SubNS))
                      for (clang::NamedDecl *VND : ViewsR)
                        if (auto *VNS = llvm::dyn_cast<clang::NamespaceDecl>(VND))
                          collectFromCtx(VNS);
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  struct MemberItem {
    std::string Typed;
    std::string Display;
    std::string SortKey;
  };

  static bool isPublic(const clang::Decl *D) {
    return D->getAccess() == clang::AS_public || D->getAccess() == clang::AS_none;
  }

  // Shortens what a type prints as, for a hint: the strings and views of
  // libc++ by their everyday names.
  static std::string shortTypeName(clang::QualType T, const clang::ASTContext &Ctx) {
    if (T.isNull())
      return "?";
    clang::PrintingPolicy PP(Ctx.getLangOpts());
    PP.SuppressScope = true;
    std::string S = T.getNonReferenceType().getUnqualifiedType().getAsString(PP);
    if (S.find("basic_string_view") != std::string::npos)
      return "string_view";
    if (S.find("basic_string") != std::string::npos)
      return "string";
    if (S.size() > 40)
      S = S.substr(0, 37) + "...";
    return S;
  }

  // The members of a record that a user may name: its own and its public
  // bases', public, not the implementation's (`__x`), each once -- the most
  // derived one where a base's has the same name.
  static void collectMembers(const clang::CXXRecordDecl *RD,
                             llvm::StringRef Prefix, bool OnlyFields,
                             std::vector<MemberItem> &Items,
                             std::set<std::string> &Seen, unsigned Depth = 0) {
    if (!RD || Depth > 16)
      return;
    RD = RD->getDefinition();
    if (!RD)
      return;
    const clang::ASTContext &Ctx = RD->getASTContext();

    for (const clang::FieldDecl *FD : RD->fields()) {
      if (!FD->getIdentifier() || !isPublic(FD))
        continue;
      llvm::StringRef FName = FD->getName();
      if (!FName.starts_with(Prefix) || FName.starts_with("__"))
        continue;
      if (!Seen.insert(FName.str()).second)
        continue;
      std::string Rest = FName.substr(Prefix.size()).str();
      if (OnlyFields)
        Rest += " = ";
      std::string Disp = "\033[1;36m." + FName.str() + "\033[0m \033[90m(" +
                         shortTypeName(FD->getType(), Ctx) + ")\033[0m";
      Items.push_back({Rest, Disp, FName.str()});
    }

    if (!OnlyFields) {
      auto addMethod = [&](const clang::FunctionDecl *MD) {
        if (!MD || !MD->getIdentifier() || MD->isImplicit() || !isPublic(MD))
          return;
        if (const auto *M = llvm::dyn_cast<clang::CXXMethodDecl>(MD))
          if (llvm::isa<clang::CXXConstructorDecl, clang::CXXDestructorDecl>(M))
            return;
        llvm::StringRef MName = MD->getName();
        if (!MName.starts_with(Prefix) || MName.starts_with("__") ||
            MName == "dump")
          return;
        if (!Seen.insert(MName.str()).second)
          return;
        std::string Rest = MName.substr(Prefix.size()).str();
        Rest += (MD->getMinRequiredArguments() == 0) ? "()" : "(";
        std::string Disp = "\033[1;33m." + MName.str() + "()\033[0m";
        Items.push_back({Rest, Disp, MName.str()});
      };
      for (const clang::Decl *D : RD->decls()) {
        if (const auto *MD = llvm::dyn_cast<clang::CXXMethodDecl>(D))
          addMethod(MD);
        else if (const auto *FTD = llvm::dyn_cast<clang::FunctionTemplateDecl>(D))
          if (isPublic(FTD))
            addMethod(FTD->getTemplatedDecl());
      }
    }

    for (const clang::CXXBaseSpecifier &B : RD->bases()) {
      if (B.getAccessSpecifier() != clang::AS_public)
        continue;
      if (const clang::CXXRecordDecl *Base = B.getType()->getAsCXXRecordDecl())
        collectMembers(Base, Prefix, OnlyFields, Items, Seen, Depth + 1);
    }
  }

  static void completeRecordMembers(const clang::CXXRecordDecl *RD,
                                    llvm::StringRef Prefix,
                                    bool OnlyFields,
                                    std::vector<llvm::LineEditor::Completion> &Out) {
    std::vector<MemberItem> Items;
    std::set<std::string> Seen;
    collectMembers(RD, Prefix, OnlyFields, Items, Seen);
    std::sort(Items.begin(), Items.end(), [](const MemberItem &A, const MemberItem &B) {
      return A.SortKey < B.SortKey;
    });
    for (auto &It : Items)
      Out.emplace_back(It.Typed, It.Display);
  }

  // ---- What an expression before `.` is, from the AST ----------------------
  //
  // The completer has text, not an expression: what stands before the dot is
  // read as a chain -- a name, then `.member` or `.method(...)` steps -- and
  // each step resolved against the session's declarations. The chain's root
  // is a placeholder of a pipeline (`_`, `_1`: an element of what the
  // pipeline starts from), a range-for's variable (an element of its range),
  // a variable, or a function's result (called, or a 0-argument command,
  // which the shell calls on its own).

  struct ChainPart {
    std::string Name;
    bool Called = false;
  };

  // A function's result type: deduced where it is still `auto` -- its body
  // instantiated as a call would -- without a diagnostic reaching the user's
  // session (a SFINAE trap holds them).
  static clang::QualType returnTypeOf(clang::Sema &S, clang::FunctionDecl *FD) {
    if (!FD)
      return {};
    clang::QualType R = FD->getReturnType();
    if (R->isUndeducedType()) {
      clang::Sema::SFINAETrap Trap(S);
      if (S.DeduceReturnType(FD, FD->getLocation(), /*Diagnose=*/false))
        return {};
      R = FD->getReturnType();
      if (R->isUndeducedType())
        return {};
    }
    return R;
  }

  // The record a type names, complete -- a template's specialization
  // instantiated for it -- or none.
  static const clang::CXXRecordDecl *recordOf(clang::Sema &S, clang::QualType T) {
    if (T.isNull())
      return nullptr;
    T = T.getNonReferenceType().getUnqualifiedType();
    if (const auto *PT = T->getAs<clang::PointerType>())
      T = PT->getPointeeType().getUnqualifiedType();
    if (!T->getAsCXXRecordDecl())
      return nullptr;
    {
      clang::Sema::SFINAETrap Trap(S);
      if (!S.isCompleteType(clang::SourceLocation(), T))
        return nullptr;
    }
    const clang::CXXRecordDecl *RD = T->getAsCXXRecordDecl();
    return RD ? RD->getDefinition() : nullptr;
  }

  // A member of a record by name: its own, or a public base's.
  static clang::NamedDecl *findMember(const clang::CXXRecordDecl *RD,
                                      clang::DeclarationName Name,
                                      unsigned Depth = 0) {
    if (!RD || Depth > 16)
      return nullptr;
    RD = RD->getDefinition();
    if (!RD)
      return nullptr;
    for (clang::NamedDecl *ND : RD->lookup(Name))
      if (isPublic(ND))
        return ND;
    for (const clang::CXXBaseSpecifier &B : RD->bases()) {
      if (B.getAccessSpecifier() != clang::AS_public)
        continue;
      if (const clang::CXXRecordDecl *Base = B.getType()->getAsCXXRecordDecl())
        if (clang::NamedDecl *Found = findMember(Base, Name, Depth + 1))
          return Found;
    }
    return nullptr;
  }
  static clang::NamedDecl *findMember(const clang::CXXRecordDecl *RD,
                                      llvm::StringRef Name) {
    if (!RD)
      return nullptr;
    return findMember(RD, &RD->getASTContext().Idents.get(Name));
  }

  // The type a member gives: a field's, a static's, a method's result.
  static clang::QualType memberType(clang::Sema &S, clang::NamedDecl *ND) {
    if (!ND)
      return {};
    ND = ND->getUnderlyingDecl();
    if (auto *FD = llvm::dyn_cast<clang::FieldDecl>(ND))
      return FD->getType();
    if (auto *VD = llvm::dyn_cast<clang::VarDecl>(ND))
      return VD->getType();
    if (auto *TND = llvm::dyn_cast<clang::TypedefNameDecl>(ND))
      return TND->getUnderlyingType();
    if (auto *FD = llvm::dyn_cast<clang::FunctionDecl>(ND))
      return returnTypeOf(S, FD);
    return {};
  }

  // What a range yields: its value_type; else what its begin() points at or
  // its iterator's operator* gives; else, a template's, its first argument
  // (a container of T); an array's element.
  static clang::QualType elementTypeOf(clang::Sema &S, clang::QualType T) {
    if (T.isNull())
      return {};
    clang::ASTContext &Ctx = S.getASTContext();
    if (const clang::ArrayType *AT = Ctx.getAsArrayType(T.getNonReferenceType()))
      return AT->getElementType();
    const clang::CXXRecordDecl *RD = recordOf(S, T);
    if (!RD)
      return {};
    clang::QualType Out = memberType(S, findMember(RD, "value_type"));
    if (!Out.isNull())
      return Out;
    clang::QualType It = memberType(S, findMember(RD, "begin"));
    if (!It.isNull()) {
      if (const auto *PT = It.getNonReferenceType()->getAs<clang::PointerType>())
        return PT->getPointeeType();
      if (const clang::CXXRecordDecl *IRD = recordOf(S, It)) {
        clang::QualType Deref = memberType(
            S, findMember(IRD, Ctx.DeclarationNames.getCXXOperatorName(clang::OO_Star)));
        if (!Deref.isNull())
          return Deref.getNonReferenceType();
        Out = memberType(S, findMember(IRD, "value_type"));
        if (!Out.isNull())
          return Out;
      }
    }
    if (const auto *Spec = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD)) {
      const clang::TemplateArgumentList &Args = Spec->getTemplateArgs();
      if (Args.size() > 0 && Args[0].getKind() == clang::TemplateArgument::Type)
        return Args[0].getAsType();
    }
    return {};
  }

  // Skips a balanced (...) or {...} backwards from just past its closing
  // bracket; returns where it opens, or npos.
  static size_t skipBackBalanced(llvm::StringRef E, size_t End) {
    char Close = E[End - 1], Open = Close == ')' ? '(' : '{';
    int Depth = 0;
    for (size_t I = End; I > 0; --I) {
      char C = E[I - 1];
      if (C == Close)
        ++Depth;
      else if (C == Open && --Depth == 0)
        return I - 1;
    }
    return llvm::StringRef::npos;
  }

  // The chain ending at the end of E: `x.name`, `obj.items().front`, `ls()`.
  static std::vector<ChainPart> chainBackward(llvm::StringRef E) {
    std::vector<ChainPart> Parts;
    size_t I = E.rtrim().size();
    for (;;) {
      bool Called = false;
      if (I > 0 && E[I - 1] == ')') {
        size_t Open = skipBackBalanced(E, I);
        if (Open == llvm::StringRef::npos)
          return {};
        I = Open;
        Called = true;
      }
      size_t End = I;
      while (I > 0 && isIdentChar(E[I - 1]))
        --I;
      if (I == End)
        return {};
      Parts.insert(Parts.begin(), ChainPart{E.substr(I, End - I).str(), Called});
      if (I > 0 && E[I - 1] == '.')
        --I;
      else if (I > 1 && E[I - 1] == '>' && E[I - 2] == '-')
        I -= 2;
      else
        break;
    }
    return Parts;
  }

  // The chain starting E: what a pipeline or a range starts from -- `ls`,
  // `ls "." {.all = true}`, `obj.items()`, `lines("f")` -- its arguments
  // skipped.
  static std::vector<ChainPart> chainForward(llvm::StringRef E) {
    std::vector<ChainPart> Parts;
    E = E.ltrim();
    size_t I = 0;
    for (;;) {
      size_t Start = I;
      while (I < E.size() && isIdentChar(E[I]))
        ++I;
      // A qualified name: only its last part is looked up.
      while (I + 1 < E.size() && E[I] == ':' && E[I + 1] == ':') {
        I += 2;
        Start = I;
        while (I < E.size() && isIdentChar(E[I]))
          ++I;
      }
      if (I == Start)
        break;
      ChainPart Part{E.substr(Start, I - Start).str(), false};
      size_t J = I;
      while (J < E.size() && E[J] == ' ')
        ++J;
      if (J < E.size() && E[J] == '(') {
        int Depth = 0;
        for (; J < E.size(); ++J) {
          if (E[J] == '(')
            ++Depth;
          else if (E[J] == ')' && --Depth == 0) {
            ++J;
            break;
          }
        }
        Part.Called = true;
        I = J;
      } else if (J > I && J < E.size() && E[J] != '.' && E[J] != '|' &&
                 E[J] != '-' && E[J] != ';') {
        // Called without parentheses, its arguments juxtaposed:
        // `lines "f"`, `ls "." {.all = true}` -- the chain ends with it.
        Part.Called = true;
        Parts.push_back(std::move(Part));
        break;
      }
      Parts.push_back(std::move(Part));
      if (I < E.size() && E[I] == '.')
        ++I;
      else if (I + 1 < E.size() && E[I] == '-' && E[I + 1] == '>')
        I += 2;
      else
        break;
    }
    return Parts;
  }

  // The statement the cursor is in: past the last `;` or `{` at the top.
  static llvm::StringRef currentStatement(llvm::StringRef Before) {
    int Depth = 0;
    for (size_t I = Before.size(); I > 0; --I) {
      char C = Before[I - 1];
      if (C == ')' || C == '}' || C == ']')
        ++Depth;
      else if (C == '(' || C == '[') {
        if (Depth > 0)
          --Depth;
      } else if (C == '{') {
        if (Depth > 0)
          --Depth;
        else
          return Before.substr(I);
      } else if (C == ';' && Depth == 0)
        return Before.substr(I);
    }
    return Before;
  }

  // A name's type: a variable's; a function's result -- called, or one the
  // shell calls on its own (a command taking nothing). An overload set
  // gives its first that resolves.
  static clang::QualType nameType(clang::Sema &S, const ChainPart &Root) {
    llvm::SmallVector<clang::NamedDecl *, 8> Decls;
    lookupDeclsByName(S, Root.Name, Decls);
    for (clang::NamedDecl *ND : Decls) {
      if (auto *VD = llvm::dyn_cast<clang::VarDecl>(ND)) {
        clang::QualType T = VD->getType();
        if (T->isUndeducedType())
          continue;
        return T;
      }
      if (auto *FD = llvm::dyn_cast<clang::FunctionDecl>(ND)) {
        if (!Root.Called && FD->getMinRequiredArguments() != 0)
          continue;
        clang::QualType T = returnTypeOf(S, FD);
        if (!T.isNull())
          return T;
      }
    }
    return {};
  }

  // A range-for's variable named in the buffer, before the cursor: the
  // range it goes over, as written (`for (auto &x : ls)` -> `ls`).
  static std::optional<std::string> loopRange(llvm::StringRef Before,
                                              llvm::StringRef Var) {
    std::string Text = Before.str();
    std::regex Loop("for\\s*\\(\\s*(?:const\\s+)?(?:auto|[A-Za-z_][\\w:<>]*)?\\s*[&*]*\\s*" +
                    Var.str() + "\\s*:");
    std::optional<std::string> Found;
    for (std::sregex_iterator It(Text.begin(), Text.end(), Loop), End; It != End; ++It) {
      size_t From = It->position() + It->length();
      int Depth = 1;
      size_t I = From;
      for (; I < Text.size(); ++I) {
        if (Text[I] == '(')
          ++Depth;
        else if (Text[I] == ')' && --Depth == 0)
          break;
      }
      Found = Text.substr(From, I - From);
    }
    return Found;
  }

  // (A member function's body sees every member of its class, wherever it
  // is declared: chainTypeImpl, below, needs no declaration here -- a class
  // member cannot be declared twice.)
  static clang::QualType chainType(clang::Sema &S, llvm::StringRef Before,
                                   const std::vector<ChainPart> &Parts,
                                   unsigned Depth = 0) {
    return chainTypeImpl(S, Before, Parts, Depth);
  }

  // What a range expression, as written, yields: where its pipeline starts
  // (before its first `|`), an element of that.
  static clang::QualType rangeElement(clang::Sema &S, llvm::StringRef Before,
                                      llvm::StringRef Range, unsigned Depth) {
    llvm::StringRef Source = Range.split('|').first.trim();
    std::vector<ChainPart> Parts = chainForward(Source);
    if (Parts.empty())
      return {};
    return elementTypeOf(S, chainType(S, Before, Parts, Depth + 1));
  }

  static clang::QualType rootType(clang::Sema &S, llvm::StringRef Before,
                                  const ChainPart &Root, unsigned Depth) {
    if (Depth > 8)
      return {};
    // A placeholder: an element of what the pipeline starts from.
    if (Root.Name == "_" || Root.Name == "_1")
      return rangeElement(S, Before, currentStatement(Before), Depth);
    // A range-for's variable: an element of its range.
    if (std::optional<std::string> Range = loopRange(Before, Root.Name)) {
      clang::QualType T = rangeElement(S, Before, *Range, Depth);
      if (!T.isNull())
        return T;
    }
    return nameType(S, Root);
  }

  static clang::QualType chainTypeImpl(clang::Sema &S, llvm::StringRef Before,
                                       const std::vector<ChainPart> &Parts,
                                       unsigned Depth) {
    if (Parts.empty())
      return {};
    clang::QualType T = rootType(S, Before, Parts.front(), Depth);
    for (size_t I = 1; I < Parts.size() && !T.isNull(); ++I)
      T = memberType(S, findMember(recordOf(S, T), Parts[I].Name));
    return T;
  }

  // ---- A command's card, on Tab after its whole name ------------------------

  struct CommandInfo {
    const char *Name;
    const char *Badge;
    bool IsPipeStage;
    const char *Examples;  // '\n'-separated
  };
  static llvm::ArrayRef<CommandInfo> commands() {
    static const CommandInfo Table[] = {
        {"ls", "dir listing", false,
         "ls\nls \".\" {.all = true}\nls | where _.size > 10_KB | sort_by(_.size)"},
        {"where", "filter rows", true, "ls | where _.is_dir"},
        {"filter", "filter rows", true, "ls | filter(_.ext == \".cpp\")"},
        {"select", "project columns", true, "ls | select(_.name)"},
        {"transform", "map elements", true, "ls | transform(_.name)"},
        {"sort_by", "sort by key", true, "ls | sort_by(_.size)"},
        {"take", "first N rows", true, "ls | take 5"},
        {"drop", "skip N rows", true, "lines \"log.txt\" | drop 10"},
        {"reverse", "reverse order", true, "ls | sort_by(_.size) | reverse"},
        {"grep", "match pattern", true, "lines \"log.txt\" | grep \"error\""},
        {"show", "render table", true, "ls | show"},
        {"lines", "read file lines", false,
         "lines \"file.txt\"\nlines \"file.txt\" | grep \"TODO\" | take 5"},
        {"cat", "print file", false, "cat \"file.txt\""},
        {"head", "first N lines", false, "head \"file.txt\" 10"},
        {"tail", "last N lines", false, "tail \"file.txt\" 10"},
        {"wc_l", "count lines", false, "wc_l \"file.txt\""},
        {"pwd", "working dir", false, "pwd"},
        {"cd", "change dir", false, "cd \"~/src\""},
        {"env", "get env var", false, "env \"HOME\""},
        {"setenv", "set env var", false, "setenv \"EDITOR\" \"vim\""},
        {"exists", "path exists", false, "exists \"build\""},
        {"mkdir_p", "create dirs", false, "mkdir_p \"out/logs\""},
        {"rm", "remove path", false, "rm \"tmp.txt\""},
        {"cp", "copy path", false, "cp \"a.txt\" \"b.txt\""},
        {"mv", "move path", false, "mv \"a.txt\" \"b.txt\""},
        {"touch", "touch file", false, "touch \"new.txt\""},
        {"run", "system command", false, "run \"make -j4\""},
        {"exec", "capture command", false, "r = exec \"git status\"; r.out"},
        {"clear", "clear screen", false, "clear"},
        {"exit", "exit shell", false, "exit"},
    };
    return Table;
  }

  // The fields of a record, on one line: `.name (string)  .size (...)`.
  static std::string fieldLine(const clang::CXXRecordDecl *RD) {
    std::vector<llvm::LineEditor::Completion> Fields;
    completeRecordMembers(RD, "", /*OnlyFields=*/true, Fields);
    std::string Line;
    for (const auto &F : Fields) {
      if (!Line.empty())
        Line += "  ";
      Line += F.DisplayText;
    }
    return Line;
  }

  static bool isStringRecord(const clang::CXXRecordDecl *RD) {
    llvm::StringRef N = RD && RD->getIdentifier() ? RD->getName() : "";
    return N == "basic_string" || N == "basic_string_view" || N == "sym";
  }

  // What a command is, from the AST: each overload's signature, the options
  // a record parameter takes, what it yields (its range's elements' fields,
  // or its result's), and how it is used.
  static std::string commandCard(clang::Sema &S, llvm::StringRef Name) {
    const CommandInfo *Known = nullptr;
    for (const CommandInfo &C : commands())
      if (Name == C.Name)
        Known = &C;
    clang::ASTContext &Ctx = S.getASTContext();
    llvm::SmallVector<clang::NamedDecl *, 8> Decls;
    lookupDeclsByName(S, Name, Decls);

    const char *Bar = "\033[90m│\033[0m ";
    std::string Card = "\033[90m╭─\033[0m \033[1;32m" + Name.str() + "\033[0m";
    if (Known)
      Card += " \033[90m— " + std::string(Known->Badge) + "\033[0m";
    Card += "\n";

    std::set<std::string> Signatures;
    std::string Options, Yields;
    for (clang::NamedDecl *ND : Decls) {
      clang::FunctionDecl *FD = llvm::dyn_cast<clang::FunctionDecl>(ND);
      if (auto *FTD = llvm::dyn_cast<clang::FunctionTemplateDecl>(ND))
        FD = FTD->getTemplatedDecl();
      if (!FD)
        continue;
      std::string Sig = Name.str() + "(";
      bool First = true;
      for (const clang::ParmVarDecl *PVD : FD->parameters()) {
        if (!First)
          Sig += ", ";
        First = false;
        Sig += shortTypeName(PVD->getType(), Ctx);
        if (PVD->getIdentifier())
          Sig += " " + PVD->getName().str();
        if (PVD->hasDefaultArg())
          Sig += " = …";
        clang::QualType PT = PVD->getType().getNonReferenceType();
        if (const clang::CXXRecordDecl *RD = PT->getAsCXXRecordDecl())
          if (!isStringRecord(RD) && Options.empty()) {
            std::string Line = fieldLine(RD);
            if (!Line.empty())
              Options = "\033[1moptions\033[0m (" + shortTypeName(PT, Ctx) + "): " + Line;
          }
      }
      Sig += ")";
      if (!FD->isTemplated() && Yields.empty()) {
        clang::QualType R = returnTypeOf(S, FD);
        if (!R.isNull() && !R->isVoidType()) {
          clang::QualType Elem = elementTypeOf(S, R);
          const clang::CXXRecordDecl *ERD = recordOf(S, Elem);
          if (ERD && !isStringRecord(ERD)) {
            std::string Line = fieldLine(ERD);
            if (!Line.empty())
              Yields = "\033[1myields\033[0m (" + shortTypeName(Elem, Ctx) + "): " + Line;
          } else if (const clang::CXXRecordDecl *RRD = recordOf(S, R);
                     RRD && !isStringRecord(RRD) && Elem.isNull()) {
            std::string Line = fieldLine(RRD);
            if (!Line.empty())
              Yields = "\033[1mreturns\033[0m (" + shortTypeName(R, Ctx) + "): " + Line;
          } else {
            Sig += " -> " + shortTypeName(R, Ctx);
          }
        }
      }
      Signatures.insert(Sig);
    }
    if (Signatures.empty() && !Known)
      return {};
    for (const std::string &Sig : Signatures)
      Card += Bar + std::string("\033[1;33m") + Sig + "\033[0m\n";
    if (!Options.empty())
      Card += Bar + Options + "\n";
    if (!Yields.empty())
      Card += Bar + Yields + "\n";
    if (Known && *Known->Examples) {
      Card += Bar + std::string("\033[1mexamples\033[0m\n");
      for (llvm::StringRef Rest = Known->Examples; !Rest.empty();) {
        auto [Line, Tail] = Rest.split('\n');
        Card += Bar + std::string("  \033[36m") + Line.str() + "\033[0m\n";
        Rest = Tail;
      }
    }
    Card += "\033[90m╰─\033[0m";
    return Card;
  }

  std::vector<llvm::LineEditor::Completion> operator()(llvm::StringRef Buffer,
                                                       size_t Pos) const {
    std::vector<llvm::LineEditor::Completion> Out;
    llvm::StringRef Before = Buffer.substr(0, std::min(Pos, Buffer.size()));
    clang::Sema &S = MainInterp.getCompilerInstance()->getSema();
    clang::ASTContext &Ctx = S.getASTContext();

    // Extract current identifier prefix before cursor
    size_t IdentStart = Before.size();
    while (IdentStart > 0 && isIdentChar(Before[IdentStart - 1]))
      --IdentStart;
    llvm::StringRef Prefix = Before.substr(IdentStart);
    llvm::StringRef Prior = Before.substr(0, IdentStart);

    // 1. Designated initializer completion -- `ls {.`, `ls dir {.all =
    //    true, .`, `f(x, {.` -- what the list's designators may name: the
    //    parameters of the function it is an argument of, by name, and the
    //    fields of its record parameters. The function: the name before an
    //    open '(' the list is inside, else the head of the juxtaposition call
    //    (the statement's first word) -- not the word just before the brace
    //    (`dir`, an argument).
    if (Prior.ends_with(".")) {
      llvm::StringRef BeforeDot = Prior.drop_back(1).rtrim();
      if (BeforeDot.ends_with("{") || BeforeDot.ends_with(",")) {
        // The '{' this list opened with, and an unmatched '(' before it.
        size_t Open = llvm::StringRef::npos, Paren = llvm::StringRef::npos;
        int Depth = 0;
        for (size_t I = BeforeDot.size(); I > 0; --I) {
          char C = BeforeDot[I - 1];
          if (C == '}' || C == ')' || C == ']') {
            ++Depth;
          } else if (C == '{' || C == '(' || C == '[') {
            if (Depth > 0) {
              --Depth;
              continue;
            }
            if (C == '{' && Open == llvm::StringRef::npos) {
              Open = I - 1;
              continue;
            }
            if (C == '(' && Open != llvm::StringRef::npos)
              Paren = I - 1;
            break;
          } else if (C == ';' && Depth == 0) {
            break;
          }
        }
        std::string FnName;
        if (Open != llvm::StringRef::npos) {
          if (Paren != llvm::StringRef::npos) {
            std::vector<ChainPart> Callee = chainBackward(BeforeDot.substr(0, Paren));
            if (!Callee.empty())
              FnName = Callee.back().Name;
          } else {
            std::vector<ChainPart> Head =
                chainForward(currentStatement(BeforeDot.substr(0, Open)));
            if (!Head.empty())
              FnName = Head.front().Name;
          }
        }
        if (!FnName.empty()) {
          llvm::SmallVector<clang::NamedDecl *, 8> Decls;
          lookupDeclsByName(S, FnName, Decls);
          std::set<std::string> Seen;
          for (clang::NamedDecl *ND : Decls) {
            const clang::FunctionDecl *FD = llvm::dyn_cast<clang::FunctionDecl>(ND);
            if (auto *FTD = llvm::dyn_cast<clang::FunctionTemplateDecl>(ND))
              FD = FTD->getTemplatedDecl();
            if (!FD)
              continue;
            for (const clang::ParmVarDecl *PVD : FD->parameters()) {
              // The parameter itself, by its name (`ls {.dir = "/tmp"}`).
              if (PVD->getIdentifier()) {
                llvm::StringRef PName = PVD->getName();
                if (PName.starts_with(Prefix) && !PName.starts_with("__") &&
                    Seen.insert(PName.str()).second)
                  Out.emplace_back(PName.substr(Prefix.size()).str() + " = ",
                                   "\033[1;35m." + PName.str() + "\033[0m \033[90m(" +
                                       shortTypeName(PVD->getType(), Ctx) + ")\033[0m");
              }
              // And the fields of a record parameter (`ls {.files_only = true}`).
              clang::QualType PT = PVD->getType().getNonReferenceType();
              if (const clang::CXXRecordDecl *RD = PT->getAsCXXRecordDecl())
                if (!isStringRecord(RD))
                  completeRecordMembers(RD, Prefix, /*OnlyFields=*/true, Out);
            }
          }
          if (!Out.empty())
            return Out;
        }
      }

      // 2. Members of whatever stands before the dot -- `_.`, `x.`, `obj.`,
      //    `x.name.`, `ls().` -- its type resolved from the AST.
      if (!BeforeDot.empty() && BeforeDot.size() == Prior.size() - 1 &&
          (isIdentChar(BeforeDot.back()) || BeforeDot.back() == ')')) {
        std::vector<ChainPart> Parts = chainBackward(BeforeDot);
        if (!Parts.empty()) {
          clang::QualType T = chainType(S, Before, Parts);
          if (const clang::CXXRecordDecl *RD = recordOf(S, T)) {
            completeRecordMembers(RD, Prefix, /*OnlyFields=*/false, Out);
            if (!Out.empty())
              return Out;
          }
        }
      }

      // Where the AST cannot say (a pipeline through a lambda's result):
      // what `ls` and `lines` yield, by the command named.
      if (BeforeDot.ends_with("_") || BeforeDot.ends_with("_1")) {
        llvm::StringRef TargetStruct = "file_entry";
        if (Before.contains("lines") || Before.contains("head") ||
            Before.contains("tail"))
          TargetStruct = "line_entry";
        llvm::SmallVector<clang::NamedDecl *, 4> StructDecls;
        lookupDeclsByName(S, TargetStruct, StructDecls);
        for (clang::NamedDecl *ND : StructDecls) {
          if (auto *RD = llvm::dyn_cast<clang::CXXRecordDecl>(ND)) {
            completeRecordMembers(RD, Prefix, /*OnlyFields=*/false, Out);
            if (!Out.empty())
              return Out;
          }
        }
      }
    }

    // 3. Filesystem path completion (`cd `, `cat `, `lines `, or path with `/` or `.`)
    size_t PathStart = Before.size();
    while (PathStart > 0 && !std::isspace(static_cast<unsigned char>(Before[PathStart - 1])) &&
           Before[PathStart - 1] != '(' && Before[PathStart - 1] != '"' &&
           Before[PathStart - 1] != '\'')
      --PathStart;
    llvm::StringRef PathTok = Before.substr(PathStart);
    llvm::StringRef BeforePath = Before.substr(0, PathStart).rtrim();
    bool WantPath = PathTok.contains('/') || PathTok.starts_with(".") ||
                    PathTok.starts_with("~") ||
                    BeforePath.ends_with("cd") || BeforePath.ends_with("cat") ||
                    BeforePath.ends_with("lines") || BeforePath.ends_with("head") ||
                    BeforePath.ends_with("tail") || BeforePath.ends_with("rm");
    if (WantPath) {
      std::string DirToScan = ".";
      std::string DirPrefix;
      llvm::StringRef FilePrefix = PathTok;
      size_t Slash = PathTok.rfind('/');
      if (Slash != llvm::StringRef::npos) {
        DirPrefix = PathTok.substr(0, Slash + 1).str();
        FilePrefix = PathTok.substr(Slash + 1);
        if (llvm::StringRef(DirPrefix).starts_with("~/")) {
          if (const char *H = std::getenv("HOME"))
            DirToScan = std::string(H) + DirPrefix.substr(1);
          else
            DirToScan = DirPrefix;
        } else {
          DirToScan = DirPrefix;
        }
      }
      std::error_code EC;
      struct PathItem {
        std::string Typed;
        std::string Display;
        std::string Name;
      };
      std::vector<PathItem> PItems;
      for (llvm::sys::fs::directory_iterator It(DirToScan, EC), End;
           !EC && It != End; It.increment(EC)) {
        llvm::StringRef FName = llvm::sys::path::filename(It->path());
        if (!FilePrefix.starts_with(".") && FName.starts_with("."))
          continue;
        if (!FName.starts_with(FilePrefix))
          continue;
        bool IsDir = llvm::sys::fs::is_directory(It->path());
        std::string Suffix = IsDir ? "/" : "";
        std::string Rest = FName.substr(FilePrefix.size()).str() + Suffix;
        std::string Disp = IsDir ? ("\033[1;34m" + FName.str() + "/\033[0m")
                                 : FName.str();
        PItems.push_back({Rest, Disp, FName.str()});
      }
      std::sort(PItems.begin(), PItems.end(),
                [](const PathItem &A, const PathItem &B) { return A.Name < B.Name; });
      for (auto &PI : PItems)
        Out.emplace_back(PI.Typed, PI.Display);
      if (!Out.empty())
        return Out;
    }

    // 4. Pipeline stage or general command/symbol completion
    bool AfterPipe = Prior.rtrim().ends_with("|");
    std::set<std::string> Seen;
    for (const CommandInfo &B : commands()) {
      if (AfterPipe && !B.IsPipeStage)
        continue;
      llvm::StringRef Name(B.Name);
      if (!Name.starts_with(Prefix))
        continue;
      Seen.insert(Name.str());
      std::string Rest = Name.substr(Prefix.size()).str();
      std::string Disp = "\033[1;32m" + Name.str() + "\033[0m \033[90m(" +
                         B.Badge + ")\033[0m";
      Out.emplace_back(Rest, Disp);
    }

    // Also include user-defined functions & variables from TranslationUnitDecl
    for (clang::Decl *D : Ctx.getTranslationUnitDecl()->noload_decls()) {
      auto *ND = llvm::dyn_cast<clang::NamedDecl>(D);
      if (!ND || !ND->getIdentifier())
        continue;
      llvm::StringRef Name = ND->getName();
      if (Name.starts_with("_") || !Name.starts_with(Prefix) ||
          Name.contains("__cppsh"))
        continue;
      if (!Seen.insert(Name.str()).second)
        continue;
      if (llvm::isa<clang::FunctionDecl, clang::FunctionTemplateDecl,
                    clang::VarDecl>(ND)) {
        std::string Rest = Name.substr(Prefix.size()).str();
        std::string Disp = "\033[1;36m" + Name.str() + "\033[0m";
        Out.emplace_back(Rest, Disp);
      }
    }

    // 5. The name typed is the one completion left, whole: its card.
    if (!Prefix.empty() && Out.size() == 1 && Out.front().TypedText.empty()) {
      std::string Card = commandCard(S, Prefix);
      if (!Card.empty()) {
        Out.clear();
        Out.emplace_back("", Card);
      }
    }
    return Out;
  }
};

static bool handleShellBuiltin(llvm::StringRef Input, bool &ShouldQuit,
                               bool &LastFailed) {
  llvm::StringRef S = Input.trim();
  if (S.ends_with(";"))
    S = S.drop_back(1).trim();

  if (S == "exit" || S == "quit" || S == "%quit") {
    ShouldQuit = true;
    return true;
  }
  if (S == "clear") {
    llvm::outs() << "\033[2J\033[H";
    llvm::outs().flush();
    LastFailed = false;
    return true;
  }
  if (S == "cd" || S.starts_with("cd ")) {
    llvm::StringRef Target = S.drop_front(2).trim();
    if (Target.size() >= 2 &&
        ((Target.front() == '"' && Target.back() == '"') ||
         (Target.front() == '\'' && Target.back() == '\''))) {
      Target = Target.substr(1, Target.size() - 2);
    }
    std::string PathStr;
    if (Target.empty() || Target == "~") {
      if (const char *H = std::getenv("HOME"))
        PathStr = H;
      else
        PathStr = "/";
    } else if (Target.starts_with("~/")) {
      if (const char *H = std::getenv("HOME"))
        PathStr = std::string(H) + Target.drop_front(1).str();
      else
        PathStr = Target.str();
    } else {
      PathStr = Target.str();
    }
    if (std::error_code EC = llvm::sys::fs::set_current_path(PathStr)) {
      llvm::errs() << "cppsh: cd: " << PathStr << ": " << EC.message() << "\n";
      LastFailed = true;
    } else {
      LastFailed = false;
    }
    return true;
  }
  return false;
}

llvm::ExitOnError ExitOnErr;

int main(int argc, const char **argv) {
  if (!std::setlocale(LC_ALL, ""))
    std::setlocale(LC_ALL, "C.UTF-8");

  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  ExitOnErr.setBanner("cppsh: ");
  llvm::cl::ParseCommandLineOptions(argc, argv, "cppsh - The C++26 Shell\n");

  llvm::llvm_shutdown_obj Y;

  std::vector<const char *> ClangArgv(ClangArgs.size());
  std::transform(ClangArgs.begin(), ClangArgs.end(), ClangArgv.begin(),
                 [](const std::string &s) -> const char * { return s.data(); });
  bool HasStdFlag = false;
  for (const std::string &A : ClangArgs)
    if (llvm::StringRef(A).starts_with("-std="))
      HasStdFlag = true;
  if (!HasStdFlag)
    ClangArgv.push_back("-std=gnu++23");
  ClangArgv.push_back("-Wno-unused-result");
  ClangArgv.push_back("-Wno-unused-value");

  llvm::InitializeAllTargetInfos();
  llvm::InitializeAllTargets();
  llvm::InitializeAllTargetMCs();
  llvm::InitializeAllAsmPrinters();
  llvm::InitializeAllAsmParsers();

  auto IEB = clang::IncrementalExecutorBuilder::createDefault();
  clang::IncrementalCompilerBuilder CB;
  CB.SetCompilerArgs(ClangArgv);

  clang::IncrementalExecutorBuilder::Options ExecutorOpts;
  ExitOnErr(IEB->configure(CB, ExecutorOpts));

  std::unique_ptr<clang::CompilerInstance> CI = ExitOnErr(CB.CreateCpp());

  llvm::install_fatal_error_handler(LLVMErrorHandler,
                                    static_cast<void *>(&CI->getDiagnostics()));
  CI->LoadRequestedPlugins();

  std::unique_ptr<clang::Interpreter> Interp =
      ExitOnErr(clang::Interpreter::create(std::move(CI), std::move(IEB)));

  bool HasError = false;

  if (!NoStdSh) {
    if (auto Err = Interp->ParseAndExecute(CppShRuntimePrelude)) {
      llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      HasError = true;
    }
  }

  if (!CommandString.empty()) {
    if (auto Err = runStatements(*Interp, CommandString)) {
      llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      HasError = true;
    }
    return HasError ? EXIT_FAILURE : EXIT_SUCCESS;
  }

  for (const std::string &input : OptInputs) {
    if (auto Err = runFileOrCode(*Interp, input)) {
      llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      HasError = true;
    }
  }

  if (OptInputs.empty()) {
    llvm::LineEditor LE("cppsh");
    std::string Input;
    bool LastFailed = false;
    LE.setListCompleter(ReplListCompleter(CB, *Interp));
    LE.setHinter([&Interp](llvm::StringRef Buffer, size_t Pos) {
      return typeHint(*Interp, Buffer, Pos);
    });
    LE.setPrompt(buildBashPrompt(LastFailed));

    while (std::optional<std::string> Line = LE.readLine()) {
      // Ctrl+C (the LineEditor's "\x03"): what was typed, continued lines
      // too, dropped; the prompt's `$` red, as after a failed command.
      if (*Line == "\x03") {
        Input.clear();
        LastFailed = true;
        LE.setPrompt(buildBashPrompt(LastFailed));
        continue;
      }
      llvm::StringRef L = *Line;
      L = L.trim();
      if (L.ends_with("\\")) {
        Input += L.drop_back(1);
        if (L.starts_with('#'))
          Input += "\n";
        LE.setPrompt("\001\033[1;33m\001> \001\033[0m\001");
        continue;
      }

      Input += L;
      if (Input.empty()) {
        LE.setPrompt(buildBashPrompt(LastFailed));
        continue;
      }

      bool ShouldQuit = false;
      if (handleShellBuiltin(Input, ShouldQuit, LastFailed)) {
        Input.clear();
        if (ShouldQuit)
          break;
        LE.setPrompt(buildBashPrompt(LastFailed));
        continue;
      }

      if (Input == R"(%undo)") {
        if (auto Err = Interp->Undo()) {
          llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
          LastFailed = true;
        } else {
          LastFailed = false;
        }
      } else {
        if (auto Err = runStatements(*Interp, Input)) {
          llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
          LastFailed = true;
        } else {
          LastFailed = false;
        }
      }

      Input.clear();
      LE.setPrompt(buildBashPrompt(LastFailed));
    }
  }

  unsigned Errs =
      Interp->getCompilerInstance()->getDiagnostics().getClient()->getNumErrors();
  return (Errs || HasError) ? EXIT_FAILURE : EXIT_SUCCESS;
}
