//===--- tools/cppsh/CppSh.cpp - cppsh - the C++26 Shell ------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticFrontend.h"
#include "clang/Basic/Version.h"
#include "clang/Config/config.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Interpreter/CodeCompletion.h"
#include "clang/Interpreter/Interpreter.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Sema.h"

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

#include <cstdlib>
#include <optional>
#include <string>
#include <vector>

#if !defined(_WIN32)
#include <pwd.h>
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

static std::string getShortHostname() {
#if !defined(_WIN32)
  char Buf[256] = {};
  if (::gethostname(Buf, sizeof(Buf) - 1) == 0 && Buf[0]) {
    llvm::StringRef H(Buf);
    size_t Dot = H.find('.');
    return H.substr(0, Dot).str();
  }
#endif
  if (const char *H = std::getenv("HOSTNAME"))
    if (*H)
      return H;
  return "localhost";
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
  std::string Host = getShortHostname();
  std::string Path = getDisplayCwd();
  bool IsRoot = false;
#if !defined(_WIN32)
  IsRoot = (::geteuid() == 0);
#endif
  const char *Dollar = IsRoot ? "#" : "$";

  // Wrap non-printing ANSI escape sequences in \001...\001 for libedit EL_PROMPT_ESC.
  const char *GreenBold = "\001\033[1;32m\001";
  const char *BlueBold = "\001\033[1;34m\001";
  const char *RedBold = "\001\033[1;31m\001";
  const char *Reset = "\001\033[0m\001";

  std::string P;
  P += GreenBold + User + "@" + Host + Reset + ":";
  P += BlueBold + Path + Reset;
  if (LastFailed)
    P += std::string(RedBold) + Dollar + Reset + " ";
  else
    P += std::string(Dollar) + " ";
  return P;
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
    return Interp.ParseAndExecute(Input);

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
  return Interp.ParseAndExecute(Content);
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

  std::vector<llvm::LineEditor::Completion> operator()(llvm::StringRef Buffer,
                                                       size_t Pos) const {
    auto Err = llvm::Error::success();
    auto res = (*this)(Buffer, Pos, Err);
    if (Err)
      llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
    return res;
  }

  std::vector<llvm::LineEditor::Completion>
  operator()(llvm::StringRef Buffer, size_t Pos, llvm::Error &ErrRes) const {
    std::vector<llvm::LineEditor::Completion> Comps;
    std::vector<std::string> Results;

    auto CI = CB.CreateCpp();
    if (auto Err = CI.takeError()) {
      ErrRes = std::move(Err);
      return {};
    }

    size_t Lines =
        std::count(Buffer.begin(), std::next(Buffer.begin(), Pos), '\n') + 1;
    auto Interp = clang::Interpreter::create(std::move(*CI));
    if (auto Err = Interp.takeError()) {
      ErrRes = std::move(Err);
      return {};
    }
    auto *MainCI = (*Interp)->getCompilerInstance();
    auto CC = clang::ReplCodeCompleter();
    CC.codeComplete(MainCI, Buffer, Lines, Pos + 1,
                    MainInterp.getCompilerInstance(), Results);
    for (auto c : Results) {
      if (c.find(CC.Prefix) == 0)
        Comps.push_back(
            llvm::LineEditor::Completion(c.substr(CC.Prefix.size()), c));
    }
    return Comps;
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
    if (auto Err = Interp->ParseAndExecute(CommandString)) {
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
    LE.setPrompt(buildBashPrompt(LastFailed));

    while (std::optional<std::string> Line = LE.readLine()) {
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
        if (auto Err = Interp->ParseAndExecute(Input)) {
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
