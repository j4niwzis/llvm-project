//===------ Interpreter.cpp - Incremental Compilation and Execution -------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the component which performs incremental code
// compilation and execution.
//
//===----------------------------------------------------------------------===//

#include "DeviceOffload.h"
#include "IncrementalAction.h"
#include "IncrementalParser.h"
#include "InterpreterUtils.h"

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/TypeVisitor.h"
#include "clang/Basic/DiagnosticParse.h"
#include "clang/Basic/DiagnosticSema.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/CodeGen/CodeGenAction.h"
#include "clang/CodeGen/ObjectFilePCHContainerWriter.h"
#include "clang/Driver/Compilation.h"
#include "clang/Driver/Driver.h"
#include "clang/Driver/Job.h"
#include "clang/Driver/Tool.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/FrontendOptions.h"
#include "clang/Frontend/MultiplexConsumer.h"
#include "clang/Frontend/TextDiagnosticBuffer.h"
#include "clang/FrontendTool/Utils.h"
#include "clang/Interpreter/IncrementalExecutor.h"
#include "clang/Interpreter/Interpreter.h"
#include "clang/Interpreter/Value.h"
#include "clang/Lex/Pragma.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Lex/PreprocessorOptions.h"
#include "clang/Options/OptionUtils.h"
#include "clang/Options/Options.h"
#include "clang/Sema/Lookup.h"
#include "clang/Serialization/ASTReader.h"
#include "clang/Serialization/ModuleCache.h"
#include "clang/Serialization/ObjectFilePCHContainerReader.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/ExecutionEngine/JITSymbol.h"
#include "llvm/ExecutionEngine/Orc/EPCDynamicLibrarySearchGenerator.h"
#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Errc.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/Cloning.h" // for CloneModule
#include <cstdio>

#define DEBUG_TYPE "clang-repl"

using namespace clang;
// FIXME: Figure out how to unify with namespace init_convenience from
//        tools/clang-import-test/clang-import-test.cpp
namespace {
/// Retrieves the clang CC1 specific flags out of the compilation's jobs.
/// \returns NULL on error.
static llvm::Expected<const llvm::opt::ArgStringList *>
GetCC1Arguments(DiagnosticsEngine *Diagnostics,
                driver::Compilation *Compilation) {
  // We expect to get back exactly one Command job, if we didn't something
  // failed. Extract that job from the Compilation.
  const driver::JobList &Jobs = Compilation->getJobs();
  if (!Jobs.size())
    return llvm::createStringError(llvm::errc::not_supported,
                                   "Driver initialization failed. "
                                   "Unable to create a driver job");

  // The driver creates one device compile job per architecture (for example if
  // --offload-arch=native finds several GPUs). Only one can be used.
  unsigned NumDeviceJobs = llvm::count_if(Jobs, [](const driver::Command &C) {
    return llvm::StringRef(C.getCreator().getName()) == "clang" &&
           llvm::is_contained(C.getArguments(),
                              llvm::StringRef("-fcuda-is-device"));
  });
  if (NumDeviceJobs > 1)
    return llvm::createStringError(
        llvm::errc::not_supported,
        "Multiple device architectures are not supported. Pass a single "
        "--offload-arch");

  // The one job we find should be to invoke clang again.
  const driver::Command *Cmd = &*Jobs.begin();
  if (llvm::StringRef(Cmd->getCreator().getName()) != "clang")
    return llvm::createStringError(llvm::errc::not_supported,
                                   "Driver initialization failed");

  return &Cmd->getArguments();
}

// ASTReaderListener that captures the PIC level stored in a serialized AST
// file (PCH or PCM) so the interpreter can compare it against its own.
class PICLevelReader : public ASTReaderListener {
  unsigned &PICLevel;

public:
  PICLevelReader(unsigned &PICLevel) : PICLevel(PICLevel) {}

  bool ReadLanguageOptions(const LangOptions &LangOpts,
                           StringRef ModuleFilename, bool Complain,
                           bool AllowCompatibleDifferences) override {
    PICLevel = LangOpts.PICLevel;
    return false;
  }
};

// clang-repl always compiles position-independent code (it injects -fPIC), so a
// PCH/PCM that was built with a different PIC level is incompatible: mixing the
// two leads to relocations that may be out of range once the JIT maps code more
// than 2GB away. PICLevel is a "compatible" language option, so the ASTReader
// would otherwise accept the mismatch silently. Reject it up front.
//
// The file is probed with its own FileManager and ModuleCache (sharing only the
// VFS) so this read leaves the CompilerInstance's state untouched for the real
// load performed later by ExecuteAction().
static llvm::Error checkASTFilePICLevel(CompilerInstance &Clang,
                                        StringRef Filename) {
  llvm::IntrusiveRefCntPtr<FileManager> FileMgr(new FileManager(
      Clang.getFileSystemOpts(), Clang.getVirtualFileSystemPtr()));
  std::shared_ptr<ModuleCache> ModCache = createCrossProcessModuleCache();
  unsigned ASTPICLevel = 0;
  PICLevelReader Reader(ASTPICLevel);
  if (!ASTReader::readASTFileControlBlock(
          Filename, *FileMgr, *ModCache, Clang.getPCHContainerReader(),
          /*FindModuleFileExtensions=*/false, Reader,
          /*ValidateDiagnosticOptions=*/false) &&
      ASTPICLevel != Clang.getLangOpts().PICLevel)
    return llvm::createStringError(
        llvm::errc::not_supported,
        "AST file '%s' was built with PIC level %u, which is incompatible "
        "with clang-repl's PIC level %u",
        Filename.str().c_str(), ASTPICLevel, Clang.getLangOpts().PICLevel);
  return llvm::Error::success();
}

static llvm::Expected<std::unique_ptr<CompilerInstance>>
CreateCI(const llvm::opt::ArgStringList &Argv) {
  std::unique_ptr<CompilerInstance> Clang(new CompilerInstance());

  // Register the support for object-file-wrapped Clang modules.
  // FIXME: Clang should register these container operations automatically.
  auto PCHOps = Clang->getPCHContainerOperations();
  PCHOps->registerWriter(std::make_unique<ObjectFilePCHContainerWriter>());
  PCHOps->registerReader(std::make_unique<ObjectFilePCHContainerReader>());

  // Buffer diagnostics from argument parsing so that we can output them using
  // a well formed diagnostic object.
  DiagnosticOptions DiagOpts;
  TextDiagnosticBuffer *DiagsBuffer = new TextDiagnosticBuffer;
  DiagnosticsEngine Diags(DiagnosticIDs::create(), DiagOpts, DiagsBuffer);
  bool Success = CompilerInvocation::CreateFromArgs(
      Clang->getInvocation(), llvm::ArrayRef(Argv.begin(), Argv.size()), Diags);

  // Infer the builtin include path if unspecified.
  if (Clang->getHeaderSearchOpts().UseBuiltinIncludes &&
      Clang->getHeaderSearchOpts().ResourceDir.empty())
    Clang->getHeaderSearchOpts().ResourceDir =
        GetResourcesPath(Argv[0], nullptr);

  if (Clang->getLangOpts().CPlusPlus) {
    bool FoundIostream = false;
    for (const auto &E : Clang->getHeaderSearchOpts().UserEntries) {
      llvm::SmallString<256> P(E.Path);
      llvm::sys::path::append(P, "iostream");
      if (llvm::sys::fs::exists(P)) {
        FoundIostream = true;
        break;
      }
    }
    if (!FoundIostream) {
      static std::vector<std::string> CachedSysDirs = []() {
        std::vector<std::string> Dirs;
        for (const char *Cmd :
             {"g++ -Wp,-v -E -x c++ /dev/null 2>&1",
              "c++ -Wp,-v -E -x c++ /dev/null 2>&1",
              "clang++ -Wp,-v -E -x c++ /dev/null 2>&1"}) {
          FILE *FP = popen(Cmd, "r");
          if (!FP)
            continue;
          char Buf[1024];
          bool InList = false;
          while (fgets(Buf, sizeof(Buf), FP)) {
            llvm::StringRef Line(Buf);
            if (Line.contains("#include <...> search starts here:")) {
              InList = true;
              continue;
            }
            if (Line.contains("End of search list."))
              break;
            if (InList) {
              llvm::StringRef Dir = Line.trim();
              if (!Dir.empty() && !Dir.contains("/lib/gcc/") &&
                  !Dir.contains("/lib/clang/") &&
                  llvm::sys::fs::is_directory(Dir))
                Dirs.push_back(Dir.str());
            }
          }
          pclose(FP);
          bool HasIO = false;
          for (const auto &D : Dirs) {
            llvm::SmallString<256> P(D);
            llvm::sys::path::append(P, "iostream");
            if (llvm::sys::fs::exists(P)) {
              HasIO = true;
              break;
            }
          }
          if (HasIO)
            break;
          Dirs.clear();
        }
        return Dirs;
      }();
      if (!CachedSysDirs.empty()) {
        Clang->getHeaderSearchOpts().UserEntries.clear();
        for (const std::string &D : CachedSysDirs)
          Clang->getHeaderSearchOpts().AddPath(
              D, frontend::ExternCSystem, /*IsFramework=*/false,
              /*IgnoreSysRoot=*/true);
      }
    }
  }

  Clang->createVirtualFileSystem();

  // Create the actual diagnostics engine.
  Clang->createDiagnostics();

  DiagsBuffer->FlushDiagnostics(Clang->getDiagnostics());
  if (!Success)
    return llvm::createStringError(llvm::errc::not_supported,
                                   "Initialization failed. "
                                   "Unable to flush diagnostics");

  // FIXME: Merge with CompilerInstance::ExecuteAction.
  llvm::MemoryBuffer *MB = llvm::MemoryBuffer::getMemBuffer("").release();
  Clang->getPreprocessorOpts().addRemappedFile("<<< inputs >>>", MB);

  Clang->setTarget(TargetInfo::CreateTargetInfo(
      Clang->getDiagnostics(), Clang->getInvocation().getTargetOpts()));
  if (!Clang->hasTarget())
    return llvm::createStringError(llvm::errc::not_supported,
                                   "Initialization failed. "
                                   "Target is missing");

  Clang->getTarget().adjust(Clang->getDiagnostics(), Clang->getLangOpts(),
                            Clang->getAuxTarget());

  // Don't clear the AST before backend codegen since we do codegen multiple
  // times, reusing the same AST.
  Clang->getCodeGenOpts().ClearASTBeforeBackend = false;

  Clang->getFrontendOpts().DisableFree = false;
  Clang->getCodeGenOpts().DisableFree = false;

  // Reject any precompiled input (PCH or PCM) built with a PIC level that
  // differs from clang-repl's own, before any Interpreter/FrontendAction is
  // constructed. See checkASTFilePICLevel for the rationale.
  StringRef PCHInclude = Clang->getPreprocessorOpts().ImplicitPCHInclude;
  if (!PCHInclude.empty())
    if (llvm::Error Err = checkASTFilePICLevel(*Clang, PCHInclude))
      return std::move(Err);

  // Explicitly loaded modules: -fmodule-file=<path> and
  // -fmodule-file=<name>=<path>.
  for (StringRef ModuleFile : Clang->getFrontendOpts().ModuleFiles)
    if (llvm::Error Err = checkASTFilePICLevel(*Clang, ModuleFile))
      return std::move(Err);
  for (const auto &NameAndFile :
       Clang->getHeaderSearchOpts().PrebuiltModuleFiles)
    if (llvm::Error Err = checkASTFilePICLevel(*Clang, NameAndFile.second))
      return std::move(Err);

  return std::move(Clang);
}

static llvm::Error ExecuteIncrementalAction(CompilerInstance &CI,
                                            IncrementalAction &Act) {
  if (!CI.ExecuteAction(Act) || CI.getDiagnostics().hasErrorOccurred()) {
    return llvm::createStringError(llvm::errc::not_supported,
                                   "Failed to execute incremental action");
  }
  return llvm::Error::success();
}

// '#pragma clang repl optimize(<opt>)' sets the optimization level and size
// used to emit modules for input parsed after the pragma. <opt> is an -O flag
// spelled without the leading dash: O0, O1, O2, O3, Os or Oz.
struct PragmaReplHandler : public PragmaHandler {
  Interpreter &Interp;

  PragmaReplHandler(Interpreter &Interp)
      : PragmaHandler("repl"), Interp(Interp) {}

  void HandlePragma(Preprocessor &PP, PragmaIntroducer Introducer,
                    Token &FirstToken) override {
    Token Tok;
    PP.LexUnexpandedToken(Tok);
    if (Tok.isNot(tok::identifier) ||
        !Tok.getIdentifierInfo()->isStr("optimize")) {
      PP.Diag(Tok.getLocation(), diag::warn_pragma_expected_identifier)
          << "clang repl";
      return;
    }

    PP.LexUnexpandedToken(Tok);
    if (Tok.isNot(tok::l_paren)) {
      PP.Diag(Tok.getLocation(), diag::warn_pragma_expected_lparen)
          << "clang repl optimize";
      return;
    }

    PP.LexUnexpandedToken(Tok);
    std::string Opt = PP.getSpelling(Tok);
    // The OptimizationLevel and OptimizeSize that each -O flag sets.
    std::optional<std::pair<unsigned, unsigned>> Level =
        llvm::StringSwitch<std::optional<std::pair<unsigned, unsigned>>>(Opt)
            .Case("O0", std::pair(0U, 0U))
            .Case("O1", std::pair(1U, 0U))
            .Case("O2", std::pair(2U, 0U))
            .Case("O3", std::pair(3U, 0U))
            .Case("Os", std::pair(2U, 1U))
            .Case("Oz", std::pair(2U, 2U))
            .Default(std::nullopt);
    if (!Level) {
      PP.Diag(Tok.getLocation(), diag::warn_pragma_invalid_argument)
          << Opt << "clang repl optimize" << /*Expected=*/true
          << "'O0', 'O1', 'O2', 'O3', 'Os' or 'Oz'";
      return;
    }

    PP.LexUnexpandedToken(Tok);
    if (Tok.isNot(tok::r_paren)) {
      PP.Diag(Tok.getLocation(), diag::warn_pragma_expected_rparen)
          << "clang repl optimize";
      return;
    }

    PP.LexUnexpandedToken(Tok);
    if (Tok.isNot(tok::eod)) {
      PP.Diag(Tok.getLocation(), diag::warn_pragma_extra_tokens_at_eol)
          << "clang repl optimize";
      return;
    }

    Interp.setOptLevel(Level->first, Level->second);
  }
};

} // anonymous namespace

namespace clang {

llvm::Expected<std::unique_ptr<CompilerInstance>>
IncrementalCompilerBuilder::create(std::string TT,
                                   std::vector<const char *> &ClangArgv) {

  // If we don't know ClangArgv0 or the address of main() at this point, try
  // to guess it anyway (it's possible on some platforms).
  std::string MainExecutableName =
      llvm::sys::fs::getMainExecutable(nullptr, nullptr);

  ClangArgv.insert(ClangArgv.begin(), MainExecutableName.c_str());

  // Compile as position-independent code. This prevents the frontend from
  // marking external symbols (e.g. C++ type-info such as _ZTIPKc used for
  // exception handling) as dso_local and emitting direct PC-relative
  // references. JITLink can place the GOT entry near the JIT'd code, keeping
  // the relocation in range. Without -fPIC, a direct Delta32 relocation to a
  // host symbol may be out of range when the JIT memory is mapped more than
  // 2GB away (as on FreeBSD), breaking tests such as
  // Interpreter/simple-exception.cpp. Insert before user arguments so it can
  // still be overridden. On Windows (excluding Cygwin/MinGW) an explicit
  // -fPIC is an unsupported driver option that would drop non-x86_64 targets
  // to PIC level 0; PIC is already the forced default there where relevant,
  // so don't inject it.
  llvm::Triple TargetTriple(TT);
  if (!TargetTriple.isOSWindows() || TargetTriple.isOSCygMing())
    ClangArgv.insert(ClangArgv.begin() + 1, "-fPIC");

  // Prepending -c to force the driver to do something if no action was
  // specified. By prepending we allow users to override the default
  // action and use other actions in incremental mode.
  // FIXME: Print proper driver diagnostics if the driver flags are wrong.
  // We do C++ by default; append right after argv[0] if no "-x" given
  ClangArgv.insert(ClangArgv.end(), "-Xclang");
  ClangArgv.insert(ClangArgv.end(), "-fincremental-extensions");
  ClangArgv.insert(ClangArgv.end(), "-c");

  // Put a dummy C++ file on to ensure there's at least one compile job for the
  // driver to construct.
  ClangArgv.push_back("<<< inputs >>>");

  // Buffer diagnostics from argument parsing so that we can output them using a
  // well formed diagnostic object.
  std::unique_ptr<DiagnosticOptions> DiagOpts =
      CreateAndPopulateDiagOpts(ClangArgv);
  TextDiagnosticBuffer *DiagsBuffer = new TextDiagnosticBuffer;
  DiagnosticsEngine Diags(DiagnosticIDs::create(), *DiagOpts, DiagsBuffer);

  driver::Driver Driver(/*MainBinaryName=*/ClangArgv[0], TT, Diags);
  Driver.setCheckInputsExist(false); // the input comes from mem buffers
  llvm::ArrayRef<const char *> RF = llvm::ArrayRef(ClangArgv);
  std::unique_ptr<driver::Compilation> Compilation(Driver.BuildCompilation(RF));

  if (CompilationCB)
    if (auto Err = (*CompilationCB)(*Compilation.get()))
      return std::move(Err);

  if (Compilation->getArgs().hasArg(options::OPT_v))
    Compilation->getJobs().Print(llvm::errs(), "\n", /*Quote=*/false);

  auto ErrOrCC1Args = GetCC1Arguments(&Diags, Compilation.get());
  if (auto Err = ErrOrCC1Args.takeError())
    return std::move(Err);

  return CreateCI(**ErrOrCC1Args);
}

llvm::Expected<std::unique_ptr<CompilerInstance>>
IncrementalCompilerBuilder::CreateCpp() {
  std::string TT = TargetTriple ? *TargetTriple : llvm::sys::getProcessTriple();

  std::vector<const char *> Argv;
  Argv.reserve(5 + 1 + UserArgs.size());
  Argv.push_back("-xc++");
#ifdef __EMSCRIPTEN__
  Argv.push_back("-target");
  Argv.push_back(TT.c_str());
  Argv.push_back("-fvisibility=default");
#endif
  llvm::append_range(Argv, UserArgs);

  return IncrementalCompilerBuilder::create(TT, Argv);
}

llvm::Expected<std::unique_ptr<CompilerInstance>>
IncrementalCompilerBuilder::createOffload(bool device, OffloadType Type) {
  if (Type == OffloadType::Detect)
    return llvm::make_error<llvm::StringError>(
        "Detecting the device vendor is not supported yet.",
        llvm::inconvertibleErrorCode());

  const bool HipEnabled = Type == OffloadType::HIP;
  std::vector<const char *> Argv;
  Argv.reserve(5 + 4 + UserArgs.size());
  Argv.push_back(HipEnabled ? "-xhip" : "-xcuda");
  Argv.push_back(device ? "--cuda-device-only" : "--cuda-host-only");

  std::string SDKPathArg = HipEnabled ? "--rocm-path=" : "--cuda-path=";
  if (!DeviceSDKPath.empty()) {
    SDKPathArg += DeviceSDKPath;
    Argv.push_back(SDKPathArg.c_str());
  }

  std::string ArchArg = "--offload-arch=";
  if (!OffloadArch.empty()) {
    ArchArg += OffloadArch;
    Argv.push_back(ArchArg.c_str());
  }

  if (OffloadCUID.empty())
    OffloadCUID = llvm::utohexstr(llvm::sys::Process::GetRandomNumber(),
                                  /*LowerCase=*/true);
  std::string CUIDArg = "-cuid=" + OffloadCUID;
  Argv.push_back(CUIDArg.c_str());

  llvm::append_range(Argv, UserArgs);

  std::string TT = TargetTriple ? *TargetTriple : llvm::sys::getProcessTriple();
  return IncrementalCompilerBuilder::create(TT, Argv);
}

llvm::Expected<std::unique_ptr<CompilerInstance>>
IncrementalCompilerBuilder::CreateDevice(OffloadType Type) {
  return IncrementalCompilerBuilder::createOffload(/*device=*/true, Type);
}

llvm::Expected<std::unique_ptr<CompilerInstance>>
IncrementalCompilerBuilder::CreateHost(OffloadType Type) {
  return IncrementalCompilerBuilder::createOffload(/*device=*/false, Type);
}

Interpreter::Interpreter(std::unique_ptr<CompilerInstance> Instance,
                         llvm::Error &ErrOut,
                         std::unique_ptr<IncrementalExecutorBuilder> IEB,
                         std::unique_ptr<clang::ASTConsumer> Consumer)
    : IncrExecutorBuilder(std::move(IEB)) {
  CI = std::move(Instance);
  llvm::ErrorAsOutParameter EAO(&ErrOut);
  auto LLVMCtx = std::make_unique<llvm::LLVMContext>();
  TSCtx = std::make_unique<llvm::orc::ThreadSafeContext>(std::move(LLVMCtx));

  // Honor -mllvm options
  CI->parseLLVMArgs();

  Act = TSCtx->withContextDo([&](llvm::LLVMContext *Ctx) {
    return std::make_unique<IncrementalAction>(*CI, *Ctx, ErrOut, *this,
                                               std::move(Consumer));
  });

  if (ErrOut)
    return;

  if (llvm::Error E = ExecuteIncrementalAction(*CI, *Act)) {
    ErrOut = joinErrors(std::move(ErrOut), std::move(E));
    return;
  }

  IncrParser =
      std::make_unique<IncrementalParser>(*CI, Act.get(), ErrOut, PTUs);

  if (ErrOut)
    return;

  CI->getPreprocessor().AddPragmaHandler("clang", new PragmaReplHandler(*this));

  if (Act->getCodeGen()) {
    Act->CacheCodeGenModule();
    // The initial PTU is filled by `-include`/`-include-pch` or by CUDA
    // includes automatically.
    if (!CI->getPreprocessorOpts().Includes.empty() ||
        !CI->getPreprocessorOpts().ImplicitPCHInclude.empty()) {
      // We can't really directly pass the CachedInCodeGenModule to the Jit
      // because it will steal it, causing dangling references as explained in
      // Interpreter::Execute
      auto M = llvm::CloneModule(*Act->getCachedCodeGenModule());
      ASTContext &C = CI->getASTContext();
      IncrParser->RegisterPTU(C.getTranslationUnitDecl(), std::move(M));
    }
    if (llvm::Error Err = CreateExecutor()) {
      ErrOut = joinErrors(std::move(ErrOut), std::move(Err));
      return;
    }
  }

  // Not all frontends support code-generation, e.g. ast-dump actions don't
  if (Act->getCodeGen()) {
    // Process the PTUs that came from initialization. For example -include will
    // give us a header that's processed at initialization of the preprocessor.
    for (PartialTranslationUnit &PTU : PTUs)
      if (llvm::Error Err = Execute(PTU)) {
        ErrOut = joinErrors(std::move(ErrOut), std::move(Err));
        return;
      }
  }
}

Interpreter::~Interpreter() {
  IncrParser.reset();
  Act->FinalizeAction();
  if (DeviceParser)
    DeviceParser.reset();
  if (DeviceAct)
    DeviceAct->FinalizeAction();
  if (IncrExecutor) {
    if (llvm::Error Err = IncrExecutor->cleanUp())
      llvm::report_fatal_error(
          llvm::Twine("Failed to clean up IncrementalExecutor: ") +
          toString(std::move(Err)));
  }
}

// These better to put in a runtime header but we can't. This is because we
// can't find the precise resource directory in unittests so we have to hard
// code them.
const char *const Runtimes = R"(
    #define __CLANG_REPL__ 1
#ifdef __cplusplus
    #define EXTERN_C extern "C"
    struct __clang_Interpreter_NewTag{} __ci_newtag;
    void* operator new(__SIZE_TYPE__, void* __p, __clang_Interpreter_NewTag) noexcept;
    template <class T, class = T (*)() /*disable for arrays*/>
    void __clang_Interpreter_SetValueCopyArr(const T* Src, void* Placement, unsigned long Size) {
      for (unsigned long Idx = 0; Idx < Size; ++Idx)
        new ((void*)(((T*)Placement) + Idx), __ci_newtag) T(Src[Idx]);
    }
    template <class T, unsigned long N>
    void __clang_Interpreter_SetValueCopyArr(const T (*Src)[N], void* Placement, unsigned long Size) {
      __clang_Interpreter_SetValueCopyArr(Src[0], Placement, Size);
    }
#else
    #if __STDC_VERSION__ < 199901L
      #define CI_RESTRICT
      #define CI_INLINE
    #else
      #define CI_RESTRICT restrict
      #define CI_INLINE inline
    #endif
    #define EXTERN_C extern
    EXTERN_C void *memcpy(void *CI_RESTRICT dst, const void *CI_RESTRICT src, __SIZE_TYPE__ n);
    EXTERN_C CI_INLINE void __clang_Interpreter_SetValueCopyArr(const void* Src, void* Placement, unsigned long Size) {
      memcpy(Placement, Src, Size);
    }
#endif // __cplusplus
  EXTERN_C void *__clang_Interpreter_SetValueWithAlloc(void*, void*, void*);
  EXTERN_C void __clang_Interpreter_SetValueNoAlloc(void *This, void *OutVal, void *OpaqueType, ...);
)";

llvm::Expected<std::unique_ptr<Interpreter>> Interpreter::create(
    std::unique_ptr<CompilerInstance> CI,
    std::unique_ptr<IncrementalExecutorBuilder> IEB /*=nullptr*/) {
  llvm::Error Err = llvm::Error::success();

  auto Interp = std::unique_ptr<Interpreter>(new Interpreter(
      std::move(CI), Err, std::move(IEB), /*Consumer=*/nullptr));
  if (auto E = std::move(Err))
    return std::move(E);

  // Add runtime code and set a marker to hide it from user code. Undo will not
  // go through that.
  if (auto E = Interp->ParseAndExecute(Runtimes))
    return std::move(E);

  Interp->markUserCodeStart();

  return std::move(Interp);
}

llvm::Expected<std::unique_ptr<Interpreter>>
Interpreter::createWithDevice(std::unique_ptr<CompilerInstance> CI,
                              std::unique_ptr<CompilerInstance> DCI,
                              OffloadType Type) {
  if (Type == OffloadType::Detect)
    return llvm::make_error<llvm::StringError>(
        "Detecting the device vendor is not supported yet.",
        llvm::inconvertibleErrorCode());

  // avoid writing fat binary to disk using an in-memory virtual file system
  llvm::IntrusiveRefCntPtr<llvm::vfs::InMemoryFileSystem> IMVFS =
      std::make_unique<llvm::vfs::InMemoryFileSystem>();
  llvm::IntrusiveRefCntPtr<llvm::vfs::OverlayFileSystem> OverlayVFS =
      std::make_unique<llvm::vfs::OverlayFileSystem>(
          llvm::vfs::getRealFileSystem());
  OverlayVFS->pushOverlay(IMVFS);
  CI->createVirtualFileSystem(OverlayVFS);
  CI->createFileManager();

  llvm::Expected<std::unique_ptr<Interpreter>> InterpOrErr =
      Interpreter::create(std::move(CI));
  if (!InterpOrErr)
    return InterpOrErr;

  std::unique_ptr<Interpreter> Interp = std::move(*InterpOrErr);

  llvm::Error Err = llvm::Error::success();

  auto DeviceAct = Interp->TSCtx->withContextDo([&](llvm::LLVMContext *Ctx) {
    return std::make_unique<IncrementalAction>(*DCI, *Ctx, Err, *Interp);
  });

  if (Err)
    return std::move(Err);

  Interp->DeviceAct = std::move(DeviceAct);

  if (llvm::Error E = ExecuteIncrementalAction(*DCI, *Interp->DeviceAct))
    return std::move(E);

  // Set the finalized initial device module aside, as the host path does.
  Interp->DeviceAct->CacheCodeGenModule();

  Interp->DeviceCI = std::move(DCI);

  std::unique_ptr<IncrementalDeviceParser> DeviceParser;
  if (Type == OffloadType::HIP)
    DeviceParser = std::make_unique<IncrementalHIPDeviceParser>(
        *Interp->DeviceCI, *Interp->getCompilerInstance(),
        Interp->DeviceAct.get(), IMVFS, Err, Interp->PTUs);
  else
    DeviceParser = std::make_unique<IncrementalCUDADeviceParser>(
        *Interp->DeviceCI, *Interp->getCompilerInstance(),
        Interp->DeviceAct.get(), IMVFS, Err, Interp->PTUs);

  if (Err)
    return std::move(Err);

  Interp->DeviceParser = std::move(DeviceParser);
  return std::move(Interp);
}

CompilerInstance *Interpreter::getCompilerInstance() { return CI.get(); }
const CompilerInstance *Interpreter::getCompilerInstance() const {
  return const_cast<Interpreter *>(this)->getCompilerInstance();
}

llvm::Expected<IncrementalExecutor &> Interpreter::getExecutionEngine() {
  if (!IncrExecutor) {
    if (auto Err = CreateExecutor())
      return std::move(Err);
  }

  return *IncrExecutor.get();
}

void Interpreter::setOptLevel(unsigned OptLevel, unsigned OptSize) {
  CodeGenOptions &CGO = getCompilerInstance()->getCodeGenOpts();
  CGO.OptimizationLevel = OptLevel;
  CGO.OptimizeSize = OptSize;
  CGO.setInlining(OptLevel ? CodeGenOptions::NormalInlining
                           : CodeGenOptions::OnlyAlwaysInlining);
}

ASTContext &Interpreter::getASTContext() {
  return getCompilerInstance()->getASTContext();
}

const ASTContext &Interpreter::getASTContext() const {
  return getCompilerInstance()->getASTContext();
}

void Interpreter::markUserCodeStart() {
  assert(!InitPTUSize && "We only do this once");
  InitPTUSize = PTUs.size();
}

size_t Interpreter::getEffectivePTUSize() const {
  assert(PTUs.size() >= InitPTUSize && "empty PTU list?");
  return PTUs.size() - InitPTUSize;
}

static const char *const CppShStdModulePrelude = R"CPPSH(
#ifndef __CPPSH_STD_MODULE_LOADED__
#define __CPPSH_STD_MODULE_LOADED__ 1
#if __has_include(<iostream>)
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>
#include <array>
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <algorithm>
#include <numeric>
#include <functional>
#include <optional>
#include <variant>
#include <tuple>
#include <memory>
#include <filesystem>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#else
extern "C" {
int printf(const char *, ...);
int snprintf(char *, unsigned long, const char *, ...);
int system(const char *);
unsigned long strlen(const char *);
int strcmp(const char *, const char *);
int strncmp(const char *, const char *, unsigned long);
char *strstr(const char *, const char *);
void *malloc(unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void *memcpy(void *, const void *, unsigned long);
void *fopen(const char *, const char *);
int fclose(void *);
unsigned long fread(void *, unsigned long, unsigned long, void *);
unsigned long fwrite(const void *, unsigned long, unsigned long, void *);
char *getenv(const char *);
}
#endif

extern "C" {
int chdir(const char *);
char *getcwd(char *, unsigned long);
struct __cppsh_dirent {
  unsigned long d_ino;
  long d_off;
  unsigned short d_reclen;
  unsigned char d_type;
  char d_name[256];
};
void *opendir(const char *);
__cppsh_dirent *readdir(void *);
int closedir(void *);
int stat(const char *, void *);
}

namespace std {

template <typename A, typename B>
inline constexpr bool __cppsh_same = false;
template <typename A>
inline constexpr bool __cppsh_same<A, A> = true;

struct cppsh_str {
  char *data_ = nullptr;
  unsigned long len_ = 0;
  unsigned long cap_ = 0;

  void init_from(const char *s, unsigned long n) {
    cap_ = n + 1;
    if (cap_ < 32) cap_ = 32;
    data_ = static_cast<char *>(malloc(cap_));
    if (n && s) memcpy(data_, s, n);
    data_[n] = '\0';
    len_ = n;
  }

  cppsh_str() { init_from("", 0); }
  cppsh_str(const char *s) { init_from(s ? s : "", s ? strlen(s) : 0); }
  cppsh_str(const char *s, unsigned long n) { init_from(s, n); }
#if __has_include(<string>)
  cppsh_str(const std::string &s) { init_from(s.data(), s.size()); }
  cppsh_str(std::string_view s) { init_from(s.data(), s.size()); }
  operator std::string() const { return std::string(c_str(), len_); }
  operator std::string_view() const noexcept { return std::string_view(c_str(), len_); }
#endif
  cppsh_str(const cppsh_str &o) { init_from(o.c_str(), o.len_); }
  cppsh_str(cppsh_str &&o) noexcept : data_(o.data_), len_(o.len_), cap_(o.cap_) {
    o.data_ = nullptr;
    o.len_ = o.cap_ = 0;
  }
  cppsh_str &operator=(const cppsh_str &o) {
    if (this != &o) {
      free(data_);
      init_from(o.c_str(), o.len_);
    }
    return *this;
  }
  cppsh_str &operator=(cppsh_str &&o) noexcept {
    if (this != &o) {
      free(data_);
      data_ = o.data_;
      len_ = o.len_;
      cap_ = o.cap_;
      o.data_ = nullptr;
      o.len_ = o.cap_ = 0;
    }
    return *this;
  }
  ~cppsh_str() { free(data_); }

  void append(const char *s, unsigned long n) {
    if (!n || !s) return;
    if (!data_) init_from("", 0);
    if (len_ + n + 1 > cap_) {
      while (len_ + n + 1 > cap_) cap_ = cap_ ? cap_ * 2 : 64;
      data_ = static_cast<char *>(realloc(data_, cap_));
    }
    memcpy(data_ + len_, s, n);
    len_ += n;
    data_[len_] = '\0';
  }

  const char *c_str() const noexcept { return data_ ? data_ : ""; }
  const char *data() const noexcept { return c_str(); }
  long long size() const noexcept { return static_cast<long long>(len_); }
  long long length() const noexcept { return static_cast<long long>(len_); }
  bool empty() const noexcept { return len_ == 0; }

  bool contains(const char *sub) const noexcept {
    return sub && strstr(c_str(), sub) != nullptr;
  }
  bool starts_with(const char *pre) const noexcept {
    if (!pre) return false;
    unsigned long plen = strlen(pre);
    return len_ >= plen && strncmp(c_str(), pre, plen) == 0;
  }
  bool ends_with(const char *suf) const noexcept {
    if (!suf) return false;
    unsigned long slen = strlen(suf);
    return len_ >= slen && strcmp(c_str() + (len_ - slen), suf) == 0;
  }
  void dump() const { printf("%s\n", c_str()); }

  friend cppsh_str operator+(const cppsh_str &a, const cppsh_str &b) {
    cppsh_str res(a.c_str(), a.len_);
    res.append(b.c_str(), b.len_);
    return res;
  }
  friend cppsh_str operator+(const cppsh_str &a, const char *b) {
    cppsh_str res(a.c_str(), a.len_);
    if (b) res.append(b, strlen(b));
    return res;
  }
  friend bool operator==(const cppsh_str &a, const cppsh_str &b) {
    return strcmp(a.c_str(), b.c_str()) == 0;
  }
  friend bool operator==(const cppsh_str &a, const char *b) {
    return strcmp(a.c_str(), b ? b : "") == 0;
  }
  friend bool operator!=(const cppsh_str &a, const cppsh_str &b) {
    return strcmp(a.c_str(), b.c_str()) != 0;
  }
  friend bool operator!=(const cppsh_str &a, const char *b) {
    return strcmp(a.c_str(), b ? b : "") != 0;
  }
  friend bool operator<(const cppsh_str &a, const cppsh_str &b) {
    return strcmp(a.c_str(), b.c_str()) < 0;
  }
  friend bool operator>(const cppsh_str &a, const cppsh_str &b) {
    return strcmp(a.c_str(), b.c_str()) > 0;
  }
#if __has_include(<iostream>)
  friend std::ostream &operator<<(std::ostream &os, const cppsh_str &s) {
    return os.write(s.c_str(), s.len_);
  }
#endif
};

template <typename T>
constexpr const char *__cppsh_cstr(const T &v) {
  if constexpr (requires { v.c_str(); })
    return v.c_str();
  else if constexpr (requires { v.name.c_str(); })
    return v.name.c_str();
  else
    return static_cast<const char *>(v);
}

template <typename F>
struct cppsh_proj {
  F fn;
  template <typename T>
  constexpr decltype(auto) operator()(T &&x) const {
    return fn(static_cast<T &&>(x));
  }
  template <char... Cs>
  constexpr auto operator_unresolved() const {
    auto next = [prev = fn](auto &&x) -> decltype(auto) {
      auto &&obj = prev(static_cast<decltype(x) &&>(x));
      return obj.template __cppsh_member<Cs...>;
    };
    return cppsh_proj<decltype(next)>{next};
  }
  constexpr auto operator!() const {
    auto p = [f = fn](auto &&x) { return !f(static_cast<decltype(x) &&>(x)); };
    return cppsh_proj<decltype(p)>{p};
  }
  constexpr auto operator-() const {
    auto p = [f = fn](auto &&x) { return -f(static_cast<decltype(x) &&>(x)); };
    return cppsh_proj<decltype(p)>{p};
  }
#define CPPSH_BINOP(OP)                                                        \
  template <typename R>                                                        \
  constexpr auto operator OP(R rhs) const {                                    \
    auto p = [f = fn, r = rhs](auto &&x) {                                     \
      return f(static_cast<decltype(x) &&>(x)) OP r;                           \
    };                                                                         \
    return cppsh_proj<decltype(p)>{p};                                         \
  }
  CPPSH_BINOP(==)
  CPPSH_BINOP(!=)
  CPPSH_BINOP(<)
  CPPSH_BINOP(>)
  CPPSH_BINOP(<=)
  CPPSH_BINOP(>=)
  CPPSH_BINOP(+)
  CPPSH_BINOP(-)
  CPPSH_BINOP(*)
  CPPSH_BINOP(/)
  CPPSH_BINOP(%)
  CPPSH_BINOP(&&)
  CPPSH_BINOP(||)
#undef CPPSH_BINOP
};

struct cppsh_placeholder_root {
  template <typename T>
  constexpr T &&operator()(T &&x) const noexcept {
    return static_cast<T &&>(x);
  }
};

inline constexpr cppsh_proj<cppsh_placeholder_root> _{cppsh_placeholder_root{}};

namespace placeholders {
using std::_;
} // namespace placeholders

template <typename T>
struct cppsh_vec {
  T *data_ = nullptr;
  unsigned long size_ = 0;
  unsigned long cap_ = 0;
  cppsh_vec() = default;
  cppsh_vec(const cppsh_vec &o) {
    for (unsigned long i = 0; i < o.size_; ++i)
      push_back(o.data_[i]);
  }
  cppsh_vec(cppsh_vec &&o) noexcept
      : data_(o.data_), size_(o.size_), cap_(o.cap_) {
    o.data_ = nullptr;
    o.size_ = o.cap_ = 0;
  }
  cppsh_vec &operator=(const cppsh_vec &o) {
    if (this != &o) {
      delete[] data_;
      data_ = nullptr;
      size_ = cap_ = 0;
      for (unsigned long i = 0; i < o.size_; ++i)
        push_back(o.data_[i]);
    }
    return *this;
  }
  cppsh_vec &operator=(cppsh_vec &&o) noexcept {
    if (this != &o) {
      delete[] data_;
      data_ = o.data_;
      size_ = o.size_;
      cap_ = o.cap_;
      o.data_ = nullptr;
      o.size_ = o.cap_ = 0;
    }
    return *this;
  }
  ~cppsh_vec() { delete[] data_; }
  void push_back(const T &v) {
    if (size_ == cap_) {
      cap_ = cap_ ? cap_ * 2 : 16;
      T *nd = new T[cap_];
      for (unsigned long i = 0; i < size_; ++i)
        nd[i] = static_cast<T &&>(data_[i]);
      delete[] data_;
      data_ = nd;
    }
    data_[size_++] = v;
  }
  T *begin() { return data_; }
  T *end() { return data_ + size_; }
  const T *begin() const { return data_; }
  const T *end() const { return data_ + size_; }
  unsigned long size() const { return size_; }
  bool empty() const { return size_ == 0; }
  T &operator[](unsigned long i) { return data_[i]; }
  const T &operator[](unsigned long i) const { return data_[i]; }
};

struct line_entry {
  long long num = 0;
  cppsh_str text;
  long long size = 0;
  bool empty() const noexcept { return size == 0; }
  bool contains(const char *s) const noexcept { return text.contains(s); }
  bool starts_with(const char *s) const noexcept { return text.starts_with(s); }
  bool ends_with(const char *s) const noexcept { return text.ends_with(s); }
  const char *c_str() const noexcept { return text.c_str(); }
  void dump() const { printf("%4lld | %s\n", num, text.c_str()); }
};

template <typename Path>
inline cppsh_str read_file(const Path &p) {
  cppsh_str out;
  auto *fp = fopen(__cppsh_cstr(p), "rb");
  if (!fp)
    return out;
  char buf[4096];
  while (unsigned long n = fread(buf, 1, sizeof(buf), fp))
    out.append(buf, n);
  fclose(fp);
  return out;
}

template <typename Path>
inline cppsh_vec<line_entry> read_lines(const Path &p) {
  cppsh_vec<line_entry> out;
  cppsh_str content = read_file(p);
  if (content.empty())
    return out;
  const char *s = content.c_str();
  unsigned long len = static_cast<unsigned long>(content.size());
  unsigned long start = 0;
  long long line_no = 1;
  for (unsigned long i = 0; i <= len; ++i) {
    if (i == len || s[i] == '\n') {
      if (i == len && start == len)
        break;
      unsigned long end = i;
      if (end > start && s[end - 1] == '\r')
        --end;
      unsigned long lsize = end - start;
      out.push_back({line_no++, cppsh_str(s + start, lsize),
                     static_cast<long long>(lsize)});
      start = i + 1;
    }
  }
  return out;
}

template <typename Path>
inline cppsh_vec<line_entry> lines(const Path &p) {
  return read_lines(p);
}

template <typename Path, typename Content>
inline bool write_file(const Path &p, const Content &c) {
  auto *fp = fopen(__cppsh_cstr(p), "wb");
  if (!fp)
    return false;
  const char *s = __cppsh_cstr(c);
  unsigned long n = s ? strlen(s) : 0;
  if (n)
    fwrite(s, 1, n, fp);
  fclose(fp);
  return true;
}

template <typename Path, typename Content>
inline bool append_file(const Path &p, const Content &c) {
  auto *fp = fopen(__cppsh_cstr(p), "ab");
  if (!fp)
    return false;
  const char *s = __cppsh_cstr(c);
  unsigned long n = s ? strlen(s) : 0;
  if (n)
    fwrite(s, 1, n, fp);
  fclose(fp);
  return true;
}

template <typename Path>
inline bool file_exists(const Path &p) {
  alignas(8) unsigned char stbuf[256] = {0};
  return stat(__cppsh_cstr(p), stbuf) == 0;
}

template <typename T>
void print(const T &v) {
  if constexpr (requires { v.c_str(); })
    printf("%s\n", v.c_str());
  else if constexpr (requires { static_cast<const char *>(v); })
    printf("%s\n", static_cast<const char *>(v));
  else if constexpr (requires { v.dump(); })
    v.dump();
  else if constexpr (__cppsh_same<T, double> || __cppsh_same<T, float>)
    printf("%g\n", (double)v);
  else
    printf("%lld\n", (long long)v);
}

template <typename Pred>
struct cppsh_filter_stage {
  Pred pred;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_filter_stage &s) {
    Rng out;
    for (auto &&item : rng)
      if (s.pred(item))
        out.push_back(item);
    return out;
  }
};
template <typename Pred>
constexpr auto filter(Pred p) {
  return cppsh_filter_stage<Pred>{p};
}

template <typename Proj>
struct cppsh_sort_stage {
  Proj proj;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_sort_stage &s) {
    for (unsigned long i = 0; i < rng.size(); ++i)
      for (unsigned long j = i + 1; j < rng.size(); ++j)
        if (s.proj(rng[j]) < s.proj(rng[i])) {
          auto tmp = rng[i];
          rng[i] = rng[j];
          rng[j] = tmp;
        }
    return rng;
  }
};
template <typename Proj>
constexpr auto sort_by(Proj p) {
  return cppsh_sort_stage<Proj>{p};
}

struct cppsh_take_stage {
  unsigned long n;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_take_stage &s) {
    Rng out;
    unsigned long i = 0;
    for (auto &&item : rng) {
      if (i++ >= s.n)
        break;
      out.push_back(item);
    }
    return out;
  }
};
inline constexpr auto take(unsigned long n) { return cppsh_take_stage{n}; }

struct cppsh_drop_stage {
  unsigned long n;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_drop_stage &s) {
    Rng out;
    unsigned long i = 0;
    for (auto &&item : rng) {
      if (i++ < s.n)
        continue;
      out.push_back(item);
    }
    return out;
  }
};
inline constexpr auto drop(unsigned long n) { return cppsh_drop_stage{n}; }

template <typename Fn>
struct cppsh_transform_stage {
  Fn fn;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_transform_stage &s) {
    using ElemT = decltype(s.fn(*rng.begin()));
    cppsh_vec<ElemT> out;
    for (auto &&item : rng)
      out.push_back(s.fn(item));
    return out;
  }
};
template <typename Fn>
constexpr auto transform(Fn f) {
  return cppsh_transform_stage<Fn>{f};
}

struct cppsh_grep_stage {
  const char *pat;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_grep_stage &g) {
    Rng out;
    for (auto &&item : rng) {
      if constexpr (requires { item.text; }) {
        if (item.text.contains(g.pat))
          out.push_back(item);
      } else if constexpr (requires { item.name; }) {
        if (item.name.contains(g.pat))
          out.push_back(item);
      } else if constexpr (requires { item.c_str(); }) {
        if (strstr(item.c_str(), g.pat) != nullptr)
          out.push_back(item);
      }
    }
    return out;
  }
};
template <typename Pat>
constexpr auto grep(const Pat &p) {
  return cppsh_grep_stage{__cppsh_cstr(p)};
}

struct cppsh_print_stage {
  template <typename Rng>
  friend void operator|(const Rng &rng, const cppsh_print_stage &) {
    for (const auto &item : rng) {
      if constexpr (requires { item.dump(); })
        item.dump();
      else
        print(item);
    }
  }
};
inline constexpr cppsh_print_stage show{};

namespace sh {

template <char... Cs>
struct sym {
  static constexpr const char value[sizeof...(Cs) + 1] = {Cs..., '\0'};
  constexpr operator const char *() const noexcept { return value; }
  operator cppsh_str() const { return cppsh_str(value); }
  constexpr const char *c_str() const noexcept { return value; }
  constexpr unsigned long size() const noexcept { return sizeof...(Cs); }
  template <char... NextCs>
  constexpr auto operator_unresolved() const noexcept {
    return sym<Cs..., '.', NextCs...>{};
  }
  constexpr auto operator-() const noexcept { return sym<'-', Cs...>{}; }
  constexpr auto operator--() const noexcept { return sym<'-', '-', Cs...>{}; }
  template <char... RCs>
  constexpr auto operator-(sym<RCs...>) const noexcept {
    return sym<Cs..., '-', RCs...>{};
  }
  template <char... RCs>
  constexpr auto operator/(sym<RCs...>) const noexcept {
    return sym<Cs..., '/', RCs...>{};
  }
  template <typename... Args>
  int operator()(Args &&...args) const {
    char cmd[2048];
    unsigned long pos = 0;
    auto appendStr = [&](const char *s) {
      while (s && *s && pos + 1 < sizeof(cmd))
        cmd[pos++] = *s++;
      cmd[pos] = '\0';
    };
    appendStr(value);
    auto appendOne = [&](const auto &a) {
      appendStr(" ");
      if constexpr (requires { static_cast<const char *>(a); }) {
        appendStr(static_cast<const char *>(a));
      } else if constexpr (requires { a.c_str(); }) {
        appendStr(a.c_str());
      } else {
        char num[64];
        snprintf(num, sizeof(num), "%lld", (long long)a);
        appendStr(num);
      }
    };
    (appendOne(args), ...);
    return system(cmd);
  }
};

template <char... Cs>
constexpr auto operator_unresolved() noexcept {
  return sym<Cs...>{};
}

struct file_entry {
  cppsh_str name;
  cppsh_str ext;
  long long size = 0;
  bool is_dir = false;
  void dump() const {
    printf("%s %-28s %10lld B\n", is_dir ? "[dir] " : "[file]", name.c_str(),
           size);
  }
};

struct ls_opts {
  bool all = false;
  bool recursive = false;
  bool dirs_only = false;
  bool files_only = false;
};

inline cppsh_vec<file_entry> ls(const char *dir = ".", ls_opts opts = {}) {
  if (dir && dir[0] == '-') {
    for (const char *p = dir + 1; *p; ++p)
      if (*p == 'a')
        opts.all = true;
    dir = ".";
  }
  cppsh_vec<file_entry> out;
  void *d = opendir(dir);
  if (!d)
    return out;
  while (__cppsh_dirent *de = readdir(d)) {
    const char *fname = de->d_name;
    if (strcmp(fname, ".") == 0 || strcmp(fname, "..") == 0)
      continue;
    if (!opts.all && fname[0] == '.')
      continue;
    bool isDir = (de->d_type == 4);
    char fullpath[1024];
    snprintf(fullpath, sizeof(fullpath), "%s/%s", dir, fname);
    alignas(8) unsigned char stbuf[256] = {0};
    long long fsize = 0;
    if (stat(fullpath, stbuf) == 0) {
      unsigned int mode = *reinterpret_cast<unsigned int *>(stbuf + 24);
      isDir = ((mode & 0170000) == 0040000);
      if (!isDir)
        fsize = *reinterpret_cast<long long *>(stbuf + 48);
    }
    if (opts.dirs_only && !isDir)
      continue;
    if (opts.files_only && isDir)
      continue;
    const char *dot = nullptr;
    for (const char *p = fname; *p; ++p)
      if (*p == '.')
        dot = p;
    out.push_back({cppsh_str(fname), cppsh_str(dot ? dot : ""), fsize, isDir});
  }
  closedir(d);
  return out;
}

template <typename Path>
inline void cat(const Path &p) {
  cppsh_str s = read_file(p);
  if (!s.empty())
    printf("%s%s", s.c_str(), s.ends_with("\n") ? "" : "\n");
}

inline cppsh_str pwd() {
  char buf[1024];
  if (getcwd(buf, sizeof(buf)))
    return cppsh_str(buf);
  return cppsh_str(".");
}

template <typename Path>
inline int cd(const Path &p) {
  return chdir(__cppsh_cstr(p));
}

template <typename Name>
inline cppsh_str env(const Name &n) {
  const char *v = getenv(__cppsh_cstr(n));
  return cppsh_str(v ? v : "");
}

using std::_;
using std::append_file;
using std::drop;
using std::file_exists;
using std::filter;
using std::grep;
using std::line_entry;
using std::lines;
using std::print;
using std::read_file;
using std::read_lines;
using std::show;
using std::sort_by;
using std::take;
using std::transform;
using std::write_file;

} // namespace sh

using sh::operator_unresolved;

} // namespace std

constexpr unsigned long long operator""_KB(unsigned long long v) noexcept {
  return v * 1024ULL;
}
constexpr unsigned long long operator""_MB(unsigned long long v) noexcept {
  return v * 1024ULL * 1024ULL;
}
constexpr unsigned long long operator""_GB(unsigned long long v) noexcept {
  return v * 1024ULL * 1024ULL * 1024ULL;
}
#endif
)CPPSH";

static std::string expandCppshStdImports(llvm::StringRef Code) {
  if (!Code.contains("import"))
    return Code.str();
  std::string Out;
  llvm::SmallVector<llvm::StringRef, 16> Lines;
  Code.split(Lines, '\n');
  for (size_t I = 0; I < Lines.size(); ++I) {
    llvm::StringRef L = Lines[I];
    llvm::StringRef Trimmed = L.trim();
    if (Trimmed.starts_with("import ") || Trimmed.starts_with("import\t")) {
      llvm::StringRef Rest = Trimmed.drop_front(6).ltrim();
      if (Rest == "std;" || Rest == "std" || Rest.starts_with("std;")) {
        Out += CppShStdModulePrelude;
        Out += "\n";
        if (Rest.starts_with("std;"))
          Out += Rest.drop_front(4).str();
        Out += "\n";
        continue;
      }
      if (Rest == "std.sh;" || Rest == "std.sh" ||
          Rest.starts_with("std.sh;")) {
        Out += CppShStdModulePrelude;
        Out += "\nusing namespace std;\nusing namespace std::sh;\n";
        if (Rest.starts_with("std.sh;"))
          Out += Rest.drop_front(7).str();
        Out += "\n";
        continue;
      }
      if (Rest == "std.compat;" || Rest == "std.compat" ||
          Rest.starts_with("std.compat;")) {
        Out += CppShStdModulePrelude;
        Out += "\nusing namespace std;\n";
        if (Rest.starts_with("std.compat;"))
          Out += Rest.drop_front(11).str();
        Out += "\n";
        continue;
      }
    }
    Out += L.str();
    if (I + 1 < Lines.size())
      Out += "\n";
  }
  return Out;
}

llvm::Expected<PartialTranslationUnit &>
Interpreter::Parse(llvm::StringRef Code) {
  std::string ExpandedCode = expandCppshStdImports(Code);
  Code = ExpandedCode;
  // If we have a device parser, parse it first. The generated code will be
  // included in the host compilation
  if (DeviceParser) {
    llvm::Expected<TranslationUnitDecl *> DeviceTU = DeviceParser->Parse(Code);
    if (auto E = DeviceTU.takeError())
      return std::move(E);

    PartialTranslationUnit &DevicePTU = DeviceParser->RegisterPTU(*DeviceTU);

    // Under -emit-llvm, print the device module IR before it is lowered.
    if (DevicePTU.TheModule &&
        DeviceCI->getFrontendOpts().ProgramAction == frontend::EmitLLVM)
      DevicePTU.TheModule->print(llvm::outs(), /*AAW=*/nullptr);

    llvm::Error Err = DeviceParser->GenerateOffloadBinary();
    if (Err)
      return std::move(Err);
  }

  // Tell the interpreter sliently ignore unused expressions since value
  // printing could cause it.
  getCompilerInstance()->getDiagnostics().setSeverity(
      clang::diag::warn_unused_expr, diag::Severity::Ignored, SourceLocation());

  llvm::Expected<TranslationUnitDecl *> TuOrErr = IncrParser->Parse(Code);
  if (!TuOrErr)
    return TuOrErr.takeError();

  PartialTranslationUnit &LastPTU = IncrParser->RegisterPTU(*TuOrErr);

  // Under -emit-llvm, print the module IR.
  if (InitPTUSize && LastPTU.TheModule &&
      getCompilerInstance()->getFrontendOpts().ProgramAction ==
          frontend::EmitLLVM)
    LastPTU.TheModule->print(llvm::outs(), /*AAW=*/nullptr);

  return LastPTU;
}

llvm::Error Interpreter::CreateExecutor() {
  if (IncrExecutor)
    return llvm::make_error<llvm::StringError>("Operation failed. "
                                               "Execution engine exists",
                                               std::error_code());
  if (!Act->getCodeGen())
    return llvm::make_error<llvm::StringError>("Operation failed. "
                                               "No code generator available",
                                               std::error_code());

  if (!IncrExecutorBuilder)
    IncrExecutorBuilder = IncrementalExecutorBuilder::createDefault();

  // Propagate mllvm args so the wasm executor can restore them after each
  // lldMain invocation (which resets all cl options for test isolation).
  IncrExecutorBuilder->LLVMArgs = CI->getFrontendOpts().LLVMArgs;

  auto ExecutorOrErr = IncrExecutorBuilder->create(*TSCtx, CI->getTarget());
  if (ExecutorOrErr)
    IncrExecutor = std::move(*ExecutorOrErr);

  return ExecutorOrErr.takeError();
}

llvm::Error Interpreter::Execute(PartialTranslationUnit &T) {
  assert(T.TheModule);
  LLVM_DEBUG(
      llvm::dbgs() << "execute-ptu "
                   << (llvm::is_contained(PTUs, T)
                           ? std::distance(PTUs.begin(), llvm::find(PTUs, T))
                           : -1)
                   << ": [TU=" << T.TUPart << ", M=" << T.TheModule.get()
                   << " (" << T.TheModule->getName() << ")]\n");
  if (!IncrExecutor) {
    auto Err = CreateExecutor();
    if (Err)
      return Err;
  }
  // FIXME: Add a callback to retain the llvm::Module once the JIT is done.
  if (auto Err = IncrExecutor->addModule(T))
    return Err;

  if (auto Err = IncrExecutor->runCtors())
    return Err;

  return llvm::Error::success();
}

llvm::Error Interpreter::ParseAndExecute(llvm::StringRef Code, Value *V) {

  auto PTU = Parse(Code);
  if (!PTU)
    return PTU.takeError();
  if (PTU->TheModule)
    if (llvm::Error Err = Execute(*PTU))
      return Err;

  if (LastValue.isValid()) {
    if (!V) {
      LastValue.dump();
      LastValue.clear();
    } else
      *V = std::move(LastValue);
  }
  return llvm::Error::success();
}

llvm::Expected<llvm::orc::ExecutorAddr>
Interpreter::getSymbolAddress(GlobalDecl GD) const {
  if (!IncrExecutor)
    return llvm::make_error<llvm::StringError>("Operation failed. "
                                               "No execution engine",
                                               std::error_code());
  llvm::StringRef MangledName = Act->getCodeGen()->GetMangledName(GD);
  return getSymbolAddress(MangledName);
}

llvm::Expected<llvm::orc::ExecutorAddr>
Interpreter::getSymbolAddress(llvm::StringRef IRName) const {
  if (!IncrExecutor)
    return llvm::make_error<llvm::StringError>("Operation failed. "
                                               "No execution engine",
                                               std::error_code());

  return IncrExecutor->getSymbolAddress(IRName, IncrementalExecutor::IRName);
}

llvm::Expected<llvm::orc::ExecutorAddr>
Interpreter::getSymbolAddressFromLinkerName(llvm::StringRef Name) const {
  if (!IncrExecutor)
    return llvm::make_error<llvm::StringError>("Operation failed. "
                                               "No execution engine",
                                               std::error_code());

  return IncrExecutor->getSymbolAddress(Name, IncrementalExecutor::LinkerName);
}

llvm::Error Interpreter::Undo(unsigned N) {

  if (getEffectivePTUSize() == 0) {
    return llvm::make_error<llvm::StringError>("Operation failed. "
                                               "No input left to undo",
                                               std::error_code());
  } else if (N > getEffectivePTUSize()) {
    return llvm::make_error<llvm::StringError>(
        llvm::formatv(
            "Operation failed. Wanted to undo {0} inputs, only have {1}.", N,
            getEffectivePTUSize()),
        std::error_code());
  }

  for (unsigned I = 0; I < N; I++) {
    if (IncrExecutor) {
      if (llvm::Error Err = IncrExecutor->removeModule(PTUs.back()))
        return Err;
    }

    IncrParser->CleanUpPTU(PTUs.back().TUPart);
    PTUs.pop_back();
  }
  return llvm::Error::success();
}

llvm::Error Interpreter::LoadDynamicLibrary(const char *name) {
  auto EEOrErr = getExecutionEngine();
  if (!EEOrErr)
    return EEOrErr.takeError();

  return EEOrErr->LoadDynamicLibrary(name);
}
} // end namespace clang
