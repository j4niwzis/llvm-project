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
#include <optional>
#include <set>
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

  static void completeRecordMembers(const clang::CXXRecordDecl *RD,
                                    llvm::StringRef Prefix,
                                    bool OnlyFields,
                                    std::vector<llvm::LineEditor::Completion> &Out) {
    if (!RD)
      return;
    RD = RD->getDefinition();
    if (!RD)
      return;

    struct Item {
      std::string Typed;
      std::string Display;
      std::string SortKey;
    };
    std::vector<Item> Items;
    std::set<std::string> Seen;

    for (const clang::FieldDecl *FD : RD->fields()) {
      if (!FD->getIdentifier())
        continue;
      llvm::StringRef FName = FD->getName();
      if (!FName.starts_with(Prefix) || FName.starts_with("__"))
        continue;
      if (!Seen.insert(FName.str()).second)
        continue;
      std::string TypeStr = FD->getType().getAsString();
      if (TypeStr.find("basic_string") != std::string::npos)
        TypeStr = "string";
      std::string Rest = FName.substr(Prefix.size()).str();
      if (OnlyFields)
        Rest += " = ";
      std::string Disp = "\033[1;36m." + FName.str() + "\033[0m \033[90m(" +
                         TypeStr + ")\033[0m";
      Items.push_back({Rest, Disp, FName.str()});
    }

    if (!OnlyFields) {
      for (const clang::CXXMethodDecl *MD : RD->methods()) {
        if (!MD->getIdentifier() || MD->isImplicit())
          continue;
        llvm::StringRef MName = MD->getName();
        if (!MName.starts_with(Prefix) || MName.starts_with("__") ||
            MName == "dump")
          continue;
        if (!Seen.insert(MName.str()).second)
          continue;
        std::string Rest = MName.substr(Prefix.size()).str();
        Rest += (MD->getMinRequiredArguments() == 0) ? "()" : "(";
        std::string Disp = "\033[1;33m." + MName.str() + "()\033[0m";
        Items.push_back({Rest, Disp, MName.str()});
      }
    }

    std::sort(Items.begin(), Items.end(),
              [](const Item &A, const Item &B) { return A.SortKey < B.SortKey; });
    for (auto &It : Items)
      Out.emplace_back(It.Typed, It.Display);
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

    // 1. Designated initializer completion: `ls {.` or `ls({.all = true, .`
    if (Prior.ends_with(".")) {
      llvm::StringRef BeforeDot = Prior.drop_back(1).rtrim();
      if (BeforeDot.ends_with("{") || BeforeDot.ends_with(",")) {
        // Walk back to the opening '{' and find the preceding function name
        int BraceDepth = 0;
        size_t I = Prior.size();
        while (I > 0) {
          --I;
          if (Prior[I] == '}')
            ++BraceDepth;
          else if (Prior[I] == '{') {
            if (BraceDepth == 0)
              break;
            --BraceDepth;
          }
        }
        // Keep walking back past any earlier `{...}` blocks or `(`
        while (I > 0) {
          llvm::StringRef Sub = Prior.substr(0, I).rtrim();
          if (Sub.ends_with("}")) {
            int D = 0;
            size_t J = Sub.size();
            while (J > 0) {
              --J;
              if (Sub[J] == '}')
                ++D;
              else if (Sub[J] == '{') {
                if (--D == 0)
                  break;
              }
            }
            I = J;
          } else if (Sub.ends_with("(")) {
            I = Sub.size() - 1;
          } else {
            break;
          }
        }
        llvm::StringRef FnSearch = Prior.substr(0, I).rtrim();
        // Skip string literal args like `ls "." {.`
        while (!FnSearch.empty() &&
               (FnSearch.back() == '"' || FnSearch.back() == '\'')) {
          char Q = FnSearch.back();
          FnSearch = FnSearch.drop_back(1);
          size_t PosQ = FnSearch.rfind(Q);
          if (PosQ == llvm::StringRef::npos)
            break;
          FnSearch = FnSearch.substr(0, PosQ).rtrim();
        }
        size_t FnEnd = FnSearch.size();
        size_t FnStart = FnEnd;
        while (FnStart > 0 && isIdentChar(FnSearch[FnStart - 1]))
          --FnStart;
        llvm::StringRef FnName = FnSearch.substr(FnStart, FnEnd - FnStart);
        if (!FnName.empty()) {
          llvm::SmallVector<clang::NamedDecl *, 8> Decls;
          lookupDeclsByName(S, FnName, Decls);
          for (clang::NamedDecl *ND : Decls) {
            const clang::FunctionDecl *FD =
                llvm::dyn_cast<clang::FunctionDecl>(ND);
            if (auto *FTD = llvm::dyn_cast<clang::FunctionTemplateDecl>(ND))
              FD = FTD->getTemplatedDecl();
            if (!FD)
              continue;
            for (const clang::ParmVarDecl *PVD : FD->parameters()) {
              clang::QualType PT = PVD->getType().getNonReferenceType();
              if (const clang::CXXRecordDecl *RD = PT->getAsCXXRecordDecl()) {
                llvm::StringRef RName =
                    RD->getIdentifier() ? RD->getIdentifier()->getName() : "";
                if (RName != "basic_string" && RName != "basic_string_view" &&
                    RName != "sym") {
                  completeRecordMembers(RD, Prefix, /*OnlyFields=*/true, Out);
                }
              }
            }
          }
          if (!Out.empty())
            return Out;
        }
      }

      // 2. Placeholder member completion: `_.` or `_.name.`
      if (BeforeDot.ends_with("_") || BeforeDot.ends_with("_1") ||
          BeforeDot.ends_with(".name") || BeforeDot.ends_with(".ext") ||
          BeforeDot.ends_with(".text")) {
        if (BeforeDot.ends_with(".name") || BeforeDot.ends_with(".ext") ||
            BeforeDot.ends_with(".text")) {
          // Chained string member completion
          const char *StrMethods[] = {"size()",        "length()",
                                      "empty()",       "contains(",
                                      "starts_with(",  "ends_with(",
                                      "substr(",       "find(",
                                      "c_str()"};
          for (const char *M : StrMethods) {
            llvm::StringRef MS(M);
            if (MS.starts_with(Prefix)) {
              Out.emplace_back(MS.substr(Prefix.size()).str(),
                               "\033[1;33m." + MS.str() + "\033[0m");
            }
          }
          if (!Out.empty())
            return Out;
        }

        // Determine pipeline element record type (`ls` -> `file_entry`, `lines` -> `line_entry`)
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
        if (DirPrefix.starts_with("~/")) {
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
    struct CmdEntry {
      const char *Name;
      const char *Badge;
      bool IsPipeStage;
    };
    static const CmdEntry Builtins[] = {
        {"ls", "dir listing", false},
        {"where", "filter rows", true},
        {"filter", "filter rows", true},
        {"select", "project columns", true},
        {"transform", "map elements", true},
        {"sort_by", "sort by key", true},
        {"take", "first N rows", true},
        {"drop", "skip N rows", true},
        {"reverse", "reverse order", true},
        {"grep", "match pattern", true},
        {"show", "render table", true},
        {"lines", "read file lines", false},
        {"cat", "print file", false},
        {"head", "first N lines", false},
        {"tail", "last N lines", false},
        {"wc_l", "count lines", false},
        {"pwd", "working dir", false},
        {"cd", "change dir", false},
        {"env", "get env var", false},
        {"setenv", "set env var", false},
        {"exists", "path exists", false},
        {"mkdir_p", "create dirs", false},
        {"rm", "remove path", false},
        {"cp", "copy path", false},
        {"mv", "move path", false},
        {"touch", "touch file", false},
        {"run", "system command", false},
        {"exec", "capture command", false},
        {"clear", "clear screen", false},
        {"exit", "exit shell", false},
    };

    std::set<std::string> Seen;
    for (const auto &B : Builtins) {
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
