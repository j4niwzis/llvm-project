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

#include "clang/AST/StmtCXX.h"
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
#include "clang/AST/QualTypeNames.h"
#include "clang/Sema/CppshStaging.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Sema.h"
#include "llvm/ADT/ScopeExit.h"
#include <mutex>
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/bit.h"
#include "clang/Serialization/ASTReader.h"
#include "clang/Serialization/ModuleCache.h"
#include "clang/Serialization/ObjectFilePCHContainerReader.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ExecutionEngine/Orc/JITTargetMachineBuilder.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/ExecutionEngine/JITSymbol.h"
#include "llvm/ExecutionEngine/Orc/EPCDynamicLibrarySearchGenerator.h"
#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/DynamicLibrary.h"
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
#include "clang/AST/APValue.h"
#include "clang/AST/RecordLayout.h"
#include "clang/Lex/Lexer.h"
#include "clang/Frontend/TextDiagnosticBuffer.h"
#include "clang/Sema/Initialization.h"
#include "clang/Sema/Sema.h"
#include "llvm/ADT/APInt.h"
#include <cctype>
#include <set>
#include <chrono>
#include <cstring>
#include <cstdio>
#if !defined(_WIN32)
#include <sys/wait.h>
#include <unistd.h>
#endif

#define DEBUG_TYPE "clang-repl"

using namespace clang;

namespace clang {
extern std::optional<APValue> (*CppshRuntimeValueOf)(const VarDecl *);
extern Expr *(*CppshRuntimeRebuildOf)(Sema &, const VarDecl *);
} // namespace clang

// cppsh: the value an object of type T has now, at P in this process, as a
// constant -- integers, bool, floating point, enums, and arrays and records
// of them; none for what is not plain data (a pointer, a std::string, a bit
// field, a union, a virtual base). In-process execution only: the address
// is this process's.
static std::optional<APValue> cppshValueAt(ASTContext &Ctx, QualType T,
                                           const unsigned char *P,
                                           unsigned Depth = 0) {
  if (Depth > 32)
    return std::nullopt;
  T = Ctx.getCanonicalType(T).getUnqualifiedType();
  if (T->isBooleanType())
    return APValue(Ctx.MakeIntValue(*P != 0, T));
  if (T->isIntegralOrEnumerationType()) {
    unsigned Bits = Ctx.getTypeSize(T);
    llvm::APInt V(Bits, 0);
    llvm::LoadIntFromMemory(V, P, Bits / 8);
    return APValue(llvm::APSInt(V, !T->isSignedIntegerOrEnumerationType()));
  }
  if (T->isRealFloatingType()) {
    const llvm::fltSemantics &Sem = Ctx.getFloatTypeSemantics(T);
    unsigned Bits = llvm::APFloat::getSizeInBits(Sem);
    llvm::APInt V(Bits, 0);
    llvm::LoadIntFromMemory(V, P, (Bits + 7) / 8);
    return APValue(llvm::APFloat(Sem, V));
  }
  if (const ConstantArrayType *AT = Ctx.getAsConstantArrayType(T)) {
    uint64_t N = AT->getZExtSize();
    int64_t Step = Ctx.getTypeSizeInChars(AT->getElementType()).getQuantity();
    APValue Out(APValue::UninitArray(), N, N);
    for (uint64_t I = 0; I < N; ++I) {
      std::optional<APValue> E =
          cppshValueAt(Ctx, AT->getElementType(), P + I * Step, Depth + 1);
      if (!E)
        return std::nullopt;
      Out.getArrayInitializedElt(I) = std::move(*E);
    }
    return Out;
  }
  if (const CXXRecordDecl *RD = T->getAsCXXRecordDecl()) {
    if (!RD->hasDefinition())
      return std::nullopt;
    RD = RD->getDefinition();
    if (RD->isUnion() || RD->getNumVBases() || RD->isDynamicClass())
      return std::nullopt;
    const ASTRecordLayout &L = Ctx.getASTRecordLayout(RD);
    unsigned NumFields = std::distance(RD->field_begin(), RD->field_end());
    APValue Out(APValue::UninitStruct(), RD->getNumBases(), NumFields);
    unsigned BI = 0;
    for (const CXXBaseSpecifier &B : RD->bases()) {
      const CXXRecordDecl *BRD = B.getType()->getAsCXXRecordDecl();
      if (!BRD)
        return std::nullopt;
      std::optional<APValue> V = cppshValueAt(
          Ctx, B.getType(), P + L.getBaseClassOffset(BRD).getQuantity(), Depth + 1);
      if (!V)
        return std::nullopt;
      Out.getStructBase(BI++) = std::move(*V);
    }
    unsigned FI = 0;
    for (const FieldDecl *FD : RD->fields()) {
      if (FD->isBitField())
        return std::nullopt;
      int64_t Off =
          Ctx.toCharUnitsFromBits(L.getFieldOffset(FD->getFieldIndex())).getQuantity();
      std::optional<APValue> V = cppshValueAt(Ctx, FD->getType(), P + Off, Depth + 1);
      if (!V)
        return std::nullopt;
      Out.getStructField(FI++) = std::move(*V);
    }
    return Out;
  }
  return std::nullopt;
}

// The interpreter whose JIT holds the variables a value is read of.
static Interpreter *CppshActiveInterpreter = nullptr;

// A snapshot (std::sh::__cppsh_snapshot's format: a tag byte, then its body)
// read a piece at a time.
namespace {
struct CppshSnapshot {
  const unsigned char *At, *End;
  bool Failed = false;
  unsigned char byte() {
    if (At >= End) {
      Failed = true;
      return 0;
    }
    return *At++;
  }
  uint64_t u64() {
    uint64_t V = 0;
    for (int I = 0; I < 8; ++I)
      V |= uint64_t(byte()) << (8 * I);
    return V;
  }
  llvm::StringRef bytes(uint64_t N) {
    if (uint64_t(End - At) < N) {
      Failed = true;
      return {};
    }
    llvm::StringRef S(reinterpret_cast<const char *>(At), N);
    At += N;
    return S;
  }
};
} // namespace

// T initialized from Args -- directly, or from one braced list -- as a
// declaration would be; none where it cannot be.
static Expr *cppshInitialize(Sema &S, QualType T, MultiExprArg Args, bool List,
                             SourceLocation Loc) {
  Sema::SFINAETrap Trap(S);
  InitializedEntity Entity = InitializedEntity::InitializeTemporary(T);
  InitializationKind Kind = List ? InitializationKind::CreateDirectList(Loc, Loc, Loc)
                                 : InitializationKind::CreateDirect(Loc, Loc, Loc);
  InitializationSequence Seq(S, Entity, Kind, Args);
  if (!Seq)
    return nullptr;
  ExprResult Made = Seq.Perform(S, Entity, Kind, Args);
  if (!Made.isUsable() || Trap.hasErrorOccurred())
    return nullptr;
  return Made.get();
}

static Expr *cppshBraced(Sema &S, QualType T, ArrayRef<Expr *> Elems,
                         SourceLocation Loc) {
  SmallVector<Expr *, 8> Inits(Elems.begin(), Elems.end());
  ExprResult List = S.ActOnInitList(Loc, Inits, Loc);
  if (!List.isUsable())
    return nullptr;
  Expr *Args[1] = {List.get()};
  return cppshInitialize(S, T, Args, /*List=*/true, Loc);
}

// A member type of a record, as its definition names it (value_type).
static QualType cppshMemberType(Sema &S, QualType T, llvm::StringRef Name) {
  if (!S.isCompleteType(SourceLocation(), T))
    return {};
  const CXXRecordDecl *RD = T->getAsCXXRecordDecl();
  if (!RD || !RD->hasDefinition())
    return {};
  for (NamedDecl *ND : RD->getDefinition()->lookup(&S.getASTContext().Idents.get(Name)))
    if (auto *TND = dyn_cast<TypedefNameDecl>(ND->getUnderlyingDecl()))
      return TND->getUnderlyingType();
  return {};
}

// A class template specialization's type arguments, a pack's opened.
static SmallVector<QualType, 4> cppshTypeArgs(QualType T) {
  SmallVector<QualType, 4> Out;
  const auto *Spec =
      dyn_cast_or_null<ClassTemplateSpecializationDecl>(T->getAsCXXRecordDecl());
  if (!Spec)
    return Out;
  for (const TemplateArgument &A : Spec->getTemplateArgs().asArray()) {
    if (A.getKind() == TemplateArgument::Type)
      Out.push_back(A.getAsType());
    else if (A.getKind() == TemplateArgument::Pack)
      for (const TemplateArgument &P : A.pack_elements())
        if (P.getKind() == TemplateArgument::Type)
          Out.push_back(P.getAsType());
  }
  return Out;
}

// The expression that rebuilds a value of type T from its snapshot.
static Expr *cppshRebuild(Sema &S, QualType T, CppshSnapshot &R,
                          SourceLocation Loc, unsigned Depth = 0) {
  if (Depth > 64 || R.Failed)
    return nullptr;
  ASTContext &Ctx = S.getASTContext();
  T = T.getNonReferenceType().getUnqualifiedType();
  auto castTo = [&](Expr *E) -> Expr * {
    ExprResult C = S.BuildCStyleCastExpr(Loc, Ctx.getTrivialTypeSourceInfo(T, Loc), Loc, E);
    return C.isUsable() ? C.get() : nullptr;
  };
  switch (R.byte()) {
  case 'b':
    return castTo(CXXBoolLiteralExpr::Create(Ctx, R.byte() != 0, Ctx.BoolTy, Loc));
  case 'i': {
    bool Signed = R.byte() != 0;
    uint64_t V = R.u64();
    return castTo(IntegerLiteral::Create(Ctx, llvm::APInt(64, V),
                                         Signed ? Ctx.LongLongTy : Ctx.UnsignedLongLongTy, Loc));
  }
  case 'f': {
    llvm::APFloat V(llvm::APFloat::IEEEdouble(), llvm::APInt(64, R.u64()));
    return castTo(FloatingLiteral::Create(Ctx, V, /*isexact=*/true, Ctx.DoubleTy, Loc));
  }
  case 's': {
    uint64_t N = R.u64();
    llvm::StringRef Text = R.bytes(N);
    if (R.Failed)
      return nullptr;
    // The characters and their count: what a string's (pointer, size)
    // constructor takes -- a NUL inside kept.
    QualType ArrTy = Ctx.getStringLiteralArrayType(Ctx.CharTy, N);
    Expr *Lit = StringLiteral::Create(Ctx, Text, StringLiteralKind::Ordinary,
                                      /*Pascal=*/false, ArrTy, Loc);
    Expr *Len = IntegerLiteral::Create(
        Ctx, llvm::APInt(Ctx.getTypeSize(Ctx.getSizeType()), N), Ctx.getSizeType(), Loc);
    Expr *Args[2] = {Lit, Len};
    return cppshInitialize(S, T, Args, /*List=*/false, Loc);
  }
  case 'o': {
    if (R.byte() == 0)
      return cppshBraced(S, T, {}, Loc);
    Expr *V = cppshRebuild(S, cppshMemberType(S, T, "value_type"), R, Loc, Depth + 1);
    if (!V)
      return nullptr;
    Expr *Args[1] = {V};
    return cppshInitialize(S, T, Args, /*List=*/false, Loc);
  }
  case 'v': {
    uint64_t Index = R.u64();
    SmallVector<QualType, 4> Alts = cppshTypeArgs(T);
    if (Index >= Alts.size())
      return nullptr;
    Expr *V = cppshRebuild(S, Alts[Index], R, Loc, Depth + 1);
    if (!V)
      return nullptr;
    Expr *Args[1] = {V};
    return cppshInitialize(S, T, Args, /*List=*/false, Loc);
  }
  case 't': {
    uint64_t N = R.u64();
    SmallVector<QualType, 4> Elems = cppshTypeArgs(T);
    if (N != Elems.size())
      return nullptr;
    SmallVector<Expr *, 4> Args;
    for (QualType E : Elems) {
      Expr *V = cppshRebuild(S, E, R, Loc, Depth + 1);
      if (!V)
        return nullptr;
      Args.push_back(V);
    }
    return cppshInitialize(S, T, Args, /*List=*/false, Loc);
  }
  case 'l': {
    uint64_t N = R.u64();
    QualType Elem = cppshMemberType(S, T, "value_type");
    if (Elem.isNull())
      return nullptr;
    SmallVector<Expr *, 8> Elems;
    for (uint64_t I = 0; I < N; ++I) {
      Expr *V = cppshRebuild(S, Elem, R, Loc, Depth + 1);
      if (!V)
        return nullptr;
      Elems.push_back(V);
    }
    return cppshBraced(S, T, Elems, Loc);
  }
  case 'r': {
    uint64_t N = R.u64();
    if (!S.isCompleteType(SourceLocation(), T))
      return nullptr;
    const CXXRecordDecl *RD = T->getAsCXXRecordDecl();
    if (!RD || !RD->hasDefinition() || RD->getDefinition()->getNumBases())
      return nullptr;
    SmallVector<Expr *, 8> Fields;
    for (const FieldDecl *FD : RD->getDefinition()->fields()) {
      if (Fields.size() == N)
        break;
      Expr *V = cppshRebuild(S, FD->getType(), R, Loc, Depth + 1);
      if (!V)
        return nullptr;
      Fields.push_back(V);
    }
    if (Fields.size() != N)
      return nullptr;
    return cppshBraced(S, T, Fields, Loc);
  }
  default:
    return nullptr;
  }
}

// A run variable that is not plain data: rebuilt from the snapshot cppsh
// took of it before this statement (std::sh::__cppsh_snapshot), read
// through the library's __cppsh_snapshot_of. In-process execution only.
static Expr *cppshRuntimeRebuildOf(Sema &S, const VarDecl *VD) {
  if (!CppshActiveInterpreter || !VD || VD->isInvalidDecl() ||
      !VD->hasGlobalStorage() || VD->getType()->isDependentType())
    return nullptr;
  llvm::Expected<llvm::orc::ExecutorAddr> Var =
      CppshActiveInterpreter->getSymbolAddress(GlobalDecl(VD));
  if (!Var) {
    llvm::consumeError(Var.takeError());
    return nullptr;
  }
  // A C string (`h(\"..\")` handed over a const char *): the string it points
  // to, as a literal -- a pointer into the running program is no constant,
  // one to a literal is.
  {
    QualType T = VD->getType().getNonReferenceType();
    if (const auto *PT = T->getAs<PointerType>();
        PT && PT->getPointeeType()->isCharType()) {
      const void *Slot = Var->toPtr<const void *>();
      if (VD->getType()->isReferenceType())
        Slot = *static_cast<const void *const *>(Slot);
      const char *Str = *static_cast<const char *const *>(Slot);
      if (!Str)
        return nullptr;
      llvm::StringRef Text(Str, ::strnlen(Str, 1 << 16));
      ASTContext &Ctx = S.Context;
      SourceLocation Loc = VD->getLocation();
      QualType Char = Ctx.CharTy.withConst();
      Expr *Lit = StringLiteral::Create(
          Ctx, Text, StringLiteralKind::Ordinary, /*Pascal=*/false,
          Ctx.getStringLiteralArrayType(Ctx.CharTy, Text.size()), Loc);
      return S.ImpCastExprToType(Lit, Ctx.getPointerType(Char), CK_ArrayToPointerDecay)
          .get();
    }
  }
  llvm::Expected<llvm::orc::ExecutorAddr> Reader =
      CppshActiveInterpreter->getSymbolAddressFromLinkerName("__cppsh_snapshot_of");
  if (!Reader) {
    llvm::consumeError(Reader.takeError());
    return nullptr;
  }
  using ReaderFn = const char *(*)(const void *, unsigned long long *);
  unsigned long long Size = 0;
  const void *Object = Var->toPtr<const void *>();
  if (VD->getType()->isReferenceType())
    Object = *static_cast<const void *const *>(Object);
  const char *Data = Reader->toPtr<ReaderFn>()(Object, &Size);
  if (!Data)
    return nullptr;
  CppshSnapshot R{reinterpret_cast<const unsigned char *>(Data),
                  reinterpret_cast<const unsigned char *>(Data) + Size};
  return cppshRebuild(S, VD->getType(), R, VD->getLocation());
}

// A global variable's value now: found by its symbol -- one a statement
// already run defined; the current one's are not in the JIT yet, and are
// not found -- and read from memory.
static std::optional<APValue> cppshRuntimeValueOf(const VarDecl *VD) {
  if (!CppshActiveInterpreter || !VD || VD->isInvalidDecl() || !VD->hasGlobalStorage())
    return std::nullopt;
  ASTContext &Ctx = VD->getASTContext();
  // A reference (a continuation's local, as the cut handed it over): what it
  // refers to.
  const bool Ref = VD->getType()->isReferenceType();
  QualType T = VD->getType().getNonReferenceType();
  if (T->isDependentType() || T->isIncompleteType() ||
      !T.isTriviallyCopyableType(Ctx))
    return std::nullopt;
  llvm::Expected<llvm::orc::ExecutorAddr> Addr =
      CppshActiveInterpreter->getSymbolAddress(GlobalDecl(VD));
  if (!Addr) {
    llvm::consumeError(Addr.takeError());
    return std::nullopt;
  }
  if (!*Addr)
    return std::nullopt;
  const unsigned char *Object = Addr->toPtr<const unsigned char *>();
  if (Ref)
    Object = *reinterpret_cast<const unsigned char *const *>(Object);
  if (!Object)
    return std::nullopt;
  return cppshValueAt(Ctx, T, Object);
}
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
        llvm::SmallString<128> CachePath;
        llvm::sys::path::system_temp_directory(/*erasedOnReboot=*/true,
                                               CachePath);
        llvm::sys::path::append(CachePath, "cppsh_sysdirs.cache");
        if (auto MB = llvm::MemoryBuffer::getFile(CachePath)) {
          llvm::SmallVector<llvm::StringRef, 8> Lines;
          (*MB)->getBuffer().split(Lines, '\n', /*MaxSplit=*/-1,
                                   /*KeepEmpty=*/false);
          bool HasIO = false;
          for (llvm::StringRef L : Lines) {
            llvm::StringRef D = L.trim();
            if (!D.empty() && llvm::sys::fs::is_directory(D)) {
              Dirs.push_back(D.str());
              llvm::SmallString<256> P(D);
              llvm::sys::path::append(P, "iostream");
              if (llvm::sys::fs::exists(P))
                HasIO = true;
            }
          }
          if (HasIO)
            return Dirs;
          Dirs.clear();
        }
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
          if (HasIO) {
            std::error_code EC;
            llvm::raw_fd_ostream OS(CachePath, EC, llvm::sys::fs::OF_Text);
            if (!EC)
              for (const auto &D : Dirs)
                OS << D << "\n";
            break;
          }
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
    auto tryAddLibcxxDirsFrom = [&](llvm::StringRef StartPath) -> bool {
      if (StartPath.empty())
        return false;
      llvm::SmallString<256> Cur(StartPath);
      llvm::sys::fs::make_absolute(Cur);
      llvm::sys::path::remove_dots(Cur, /*remove_dot_dot=*/true);
      llvm::SmallVector<std::string, 4> PrependDirs;
      bool HasBuildLibcxx = false;
      std::string TT = Clang->getTargetOpts().Triple;
      for (int Depth = 0; Depth < 10 && !Cur.empty(); ++Depth) {
        if (!TT.empty()) {
          llvm::SmallString<256> TargetCxxDir(Cur);
          llvm::sys::path::append(TargetCxxDir, "include", TT, "c++", "v1");
          if (llvm::sys::fs::is_directory(TargetCxxDir))
            PrependDirs.push_back(std::string(TargetCxxDir.str()));
        }
        llvm::SmallString<256> BuildCxxDir(Cur);
        llvm::sys::path::append(BuildCxxDir, "include", "c++", "v1");
        llvm::SmallString<256> BuildIostream(BuildCxxDir);
        llvm::sys::path::append(BuildIostream, "iostream");
        if (llvm::sys::fs::exists(BuildIostream)) {
          PrependDirs.push_back(std::string(BuildCxxDir.str()));
          HasBuildLibcxx = true;
        }
        llvm::SmallString<256> RuntimesCxxDir(Cur);
        llvm::sys::path::append(RuntimesCxxDir, "runtimes", "runtimes-bins");
        llvm::sys::path::append(RuntimesCxxDir, "include", "c++", "v1");
        llvm::SmallString<256> RuntimesIostream(RuntimesCxxDir);
        llvm::sys::path::append(RuntimesIostream, "iostream");
        if (llvm::sys::fs::exists(RuntimesIostream)) {
          PrependDirs.push_back(std::string(RuntimesCxxDir.str()));
          HasBuildLibcxx = true;
        }
        llvm::SmallString<256> SrcCxxDir(Cur);
        llvm::sys::path::append(SrcCxxDir, "libcxx", "include");
        llvm::SmallString<256> SrcMeta(SrcCxxDir);
        llvm::sys::path::append(SrcMeta, "meta");
        if (llvm::sys::fs::exists(SrcMeta))
          PrependDirs.push_back(std::string(SrcCxxDir.str()));
        if (!PrependDirs.empty()) {
          auto &UE = Clang->getHeaderSearchOpts().UserEntries;
          if (HasBuildLibcxx) {
            Clang->getHeaderSearchOpts().UseStandardCXXIncludes = false;
            llvm::erase_if(UE, [](const HeaderSearchOptions::Entry &E) {
              return llvm::StringRef(E.Path).contains("/include/c++/");
            });
            for (auto It = PrependDirs.rbegin(); It != PrependDirs.rend(); ++It)
              UE.insert(UE.begin(),
                        HeaderSearchOptions::Entry(*It, frontend::System,
                                                   /*IsFramework=*/false,
                                                   /*IgnoreSysRoot=*/true));
          } else {
            for (const std::string &D : PrependDirs)
              Clang->getHeaderSearchOpts().AddPath(
                  D, frontend::System, /*IsFramework=*/false,
                  /*IgnoreSysRoot=*/true);
          }
          return true;
        }
        if (!llvm::sys::path::has_parent_path(Cur))
          break;
        llvm::sys::path::remove_filename(Cur);
      }
      return false;
    };
    std::string MainExe = llvm::sys::fs::getMainExecutable(nullptr, nullptr);
    if (!tryAddLibcxxDirsFrom(MainExe))
      if (!tryAddLibcxxDirsFrom(Clang->getHeaderSearchOpts().ResourceDir))
        if (Argv.empty() || !tryAddLibcxxDirsFrom(Argv[0]))
          if (!tryAddLibcxxDirsFrom("."))
            tryAddLibcxxDirsFrom(__FILE__);
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
  Argv.reserve(5 + 2 + UserArgs.size());
  Argv.push_back("-xc++");
  bool HasStd = llvm::any_of(UserArgs, [](const char *A) {
    return llvm::StringRef(A).starts_with("-std=");
  });
  if (!HasStd)
    Argv.push_back("-std=gnu++23");
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

#if defined(__SIZEOF_INT128__)
extern "C" {
LLVM_ATTRIBUTE_USED unsigned __int128
__cppsh_udivmodti4(unsigned __int128 a, unsigned __int128 b,
                   unsigned __int128 *rem) {
  if (b == 0) {
    if (rem)
      *rem = 0;
    return 0;
  }
  unsigned __int128 q = 0, r = 0;
  for (int i = 127; i >= 0; --i) {
    r = (r << 1) | ((a >> i) & 1);
    if (r >= b) {
      r -= b;
      q |= (static_cast<unsigned __int128>(1) << i);
    }
  }
  if (rem)
    *rem = r;
  return q;
}

LLVM_ATTRIBUTE_USED unsigned __int128 __cppsh_udivti3(unsigned __int128 a,
                                                      unsigned __int128 b) {
  return __cppsh_udivmodti4(a, b, nullptr);
}

LLVM_ATTRIBUTE_USED unsigned __int128 __cppsh_umodti3(unsigned __int128 a,
                                                      unsigned __int128 b) {
  unsigned __int128 r = 0;
  __cppsh_udivmodti4(a, b, &r);
  return r;
}

LLVM_ATTRIBUTE_USED __int128 __cppsh_divti3(__int128 a, __int128 b) {
  bool neg = (a < 0) != (b < 0);
  unsigned __int128 ua = a < 0 ? -static_cast<unsigned __int128>(a)
                               : static_cast<unsigned __int128>(a);
  unsigned __int128 ub = b < 0 ? -static_cast<unsigned __int128>(b)
                               : static_cast<unsigned __int128>(b);
  unsigned __int128 uq = __cppsh_udivmodti4(ua, ub, nullptr);
  return neg ? -static_cast<__int128>(uq) : static_cast<__int128>(uq);
}

LLVM_ATTRIBUTE_USED __int128 __cppsh_modti3(__int128 a, __int128 b) {
  bool neg = (a < 0);
  unsigned __int128 ua = a < 0 ? -static_cast<unsigned __int128>(a)
                               : static_cast<unsigned __int128>(a);
  unsigned __int128 ub = b < 0 ? -static_cast<unsigned __int128>(b)
                               : static_cast<unsigned __int128>(b);
  unsigned __int128 ur = 0;
  __cppsh_udivmodti4(ua, ub, &ur);
  return neg ? -static_cast<__int128>(ur) : static_cast<__int128>(ur);
}
} // extern "C"
#endif

Interpreter::Interpreter(std::unique_ptr<CompilerInstance> Instance,
                         llvm::Error &ErrOut,
                         std::unique_ptr<IncrementalExecutorBuilder> IEB,
                         std::unique_ptr<clang::ASTConsumer> Consumer)
    : IncrExecutorBuilder(std::move(IEB)) {
#if defined(__SIZEOF_INT128__)
  llvm::sys::DynamicLibrary::AddSymbol(
      "__udivmodti4", reinterpret_cast<void *>(&__cppsh_udivmodti4));
  llvm::sys::DynamicLibrary::AddSymbol(
      "__udivti3", reinterpret_cast<void *>(&__cppsh_udivti3));
  llvm::sys::DynamicLibrary::AddSymbol(
      "__umodti3", reinterpret_cast<void *>(&__cppsh_umodti3));
  llvm::sys::DynamicLibrary::AddSymbol(
      "__divti3", reinterpret_cast<void *>(&__cppsh_divti3));
  llvm::sys::DynamicLibrary::AddSymbol(
      "__modti3", reinterpret_cast<void *>(&__cppsh_modti3));
#endif
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

  // Values of run statements' variables, for the value specialization.
  if (IncrExecutor) {
    CppshActiveInterpreter = this;
    CppshRuntimeValueOf = cppshRuntimeValueOf;
    CppshRuntimeRebuildOf = cppshRuntimeRebuildOf;
  }
}

Interpreter::~Interpreter() {
  if (CppshActiveInterpreter == this) {
    CppshActiveInterpreter = nullptr;
    CppshRuntimeValueOf = nullptr;
    CppshRuntimeRebuildOf = nullptr;
  }
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

llvm::Expected<PartialTranslationUnit &>
Interpreter::Parse(llvm::StringRef Code) {
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
  // cppsh: CPPSH_TRACE_MODULE: each module added, what it defines and the
  // global variables it uses from elsewhere, with the functions using them.
  if (::getenv("CPPSH_TRACE_MODULE")) {
    llvm::Module &M = *T.TheModule;
    llvm::errs() << "cppsh-module: " << M.getName() << " defines:";
    for (llvm::GlobalValue &G : M.global_values())
      if (!G.isDeclaration())
        llvm::errs() << " " << G.getName();
    llvm::errs() << "\n";
    for (llvm::GlobalVariable &G : M.globals()) {
      if (!G.isDeclaration())
        continue;
      llvm::errs() << "cppsh-module:   uses variable " << G.getName() << " in:";
      llvm::SmallVector<llvm::User *, 8> Work(G.users());
      llvm::SmallPtrSet<llvm::User *, 16> Seen;
      while (!Work.empty()) {
        llvm::User *U = Work.pop_back_val();
        if (!Seen.insert(U).second)
          continue;
        if (auto *I = llvm::dyn_cast<llvm::Instruction>(U))
          llvm::errs() << " " << I->getFunction()->getName();
        else if (auto *GV = llvm::dyn_cast<llvm::GlobalValue>(U))
          llvm::errs() << " " << GV->getName();
        else
          Work.append(U->user_begin(), U->user_end());
      }
      llvm::errs() << "\n";
    }
  }
  // FIXME: Add a callback to retain the llvm::Module once the JIT is done.
  if (auto Err = IncrExecutor->addModule(T))
    return Err;

  if (auto Err = IncrExecutor->runCtors())
    return Err;

  return llvm::Error::success();
}

// (Inside namespace clang already.)
extern SourceLocation CppshStageAt;
extern std::vector<SourceLocation> CppshTopLevelStarts;
// What the shell does before each piece of an input is compiled (cppsh: the
// snapshots of the variables it names); none by default.
void (*CppshBeforeChunk)(Interpreter &, llvm::StringRef) = nullptr;
// How many inputs the staging probe forked for (CPPSH_TIME).
unsigned CppshProbes = 0;
// Time spent parsing (with code generation) and executing (JIT link and run),
// for CPPSH_TIME.
unsigned long long CppshParseNs = 0, CppshExecuteNs = 0;

extern std::set<const FunctionDecl *> CppshCutFunctions;
extern llvm::DenseMap<const VarDecl *, APValue> CppshParamValue;
extern llvm::DenseMap<const VarDecl *, const Expr *> CppshParamRebuild;
extern llvm::DenseSet<const VarDecl *> CppshStagedTracked;
extern bool CppshStagedLive;
extern llvm::SmallPtrSet<const VarDecl *, 8> CppshStagedWanted;
bool cppshMutates(const Stmt *S, const VarDecl *VD);
extern bool CppshTopNeed;
extern bool CppshCutNeeded;
extern std::vector<Expr *> CppshCutStagedCalls;
extern std::vector<SourceRange> CppshTopNeedExprs;
extern llvm::DenseMap<SourceLocation::UIntTy, SourceLocation>
    CppshVariantIndexNeeds;
extern SourceLocation CppshHoistBegin, CppshHoistEnd;
extern bool CppshInHoist;

// The global holding the last continuation's result: what a hoisted call is
// replaced by.
static std::string CppshLastResult;
// Every result kept, in the order kept: a statement using several staged
// calls' results takes the last as many (its calls made in order, just
// before it).
static std::vector<std::string> CppshResultHistory;
static unsigned CppshContinuations = 0;

// std::sh::<Name>, as an expression to call.
static ExprResult cppshShCallee(Sema &S, StringRef Name) {
  NamespaceDecl *Std = S.getStdNamespace();
  if (!Std)
    return ExprError();
  IdentifierTable &Idents = S.getPreprocessor().getIdentifierTable();
  LookupResult ShR(S, &Idents.get("sh"), SourceLocation(),
                   Sema::LookupNamespaceName);
  S.LookupQualifiedName(ShR, Std);
  auto *Sh = ShR.getAsSingle<NamespaceDecl>();
  if (!Sh)
    return ExprError();
  LookupResult R(S, &Idents.get(Name), SourceLocation(),
                 Sema::LookupOrdinaryName);
  S.LookupQualifiedName(R, Sh);
  if (R.empty())
    return ExprError();
  CXXScopeSpec SS;
  return S.BuildDeclarationNameExpr(SS, R, /*NeedsADL=*/false);
}

static bool cppshReport(llvm::Error Err) {
  if (!Err)
    return true;
  llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
  return false;
}

// The snapshots of variables (std::sh::__cppsh_snapshot), taken now -- a unit
// Sema builds: never text parsed in the middle of an input's tokens.
llvm::Error Interpreter::cppshSnapshot(ArrayRef<VarDecl *> Vars) {
  if (Vars.empty())
    return llvm::Error::success();
  Sema &S = getCompilerInstance()->getSema();
  ASTContext &Ctx = S.Context;
  const SourceLocation Loc;
  ExprResult Snap = cppshShCallee(S, "__cppsh_snapshot");
  if (!Snap.isUsable())
    return llvm::make_error<llvm::StringError>("cppsh: no std::sh::__cppsh_snapshot",
                                               std::error_code());
  Interpreter &Interp = *this;
  if (llvm::Error Err = cppshBeginBuild())
    return Err;
  {
    for (VarDecl *G : Vars) {
      // Each in a top-level statement's own scope, as the parser makes one
      // (cppshRunTokens).
      Parser &P = cppshParser();
      P.EnterScope(Scope::FnScope | Scope::DeclScope | Scope::CompoundStmtScope);
      TopLevelStmtDecl *Stmt = S.ActOnStartTopLevelStmtDecl(P.getCurScope());
      Expr *Ref = S.BuildDeclRefExpr(G, G->getType().getNonReferenceType(),
                                     VK_LValue, Loc);
      ExprResult Call = S.BuildCallExpr(P.getCurScope(), Snap.get(), Loc, Ref, Loc);
      ExprResult Full = Call.isUsable()
                            ? S.ActOnFinishFullExpr(Call.get(), /*DiscardedValue=*/true)
                            : ExprError();
      S.ActOnFinishTopLevelStmtDecl(
          Stmt, Full.isUsable() ? static_cast<clang::Stmt *>(Full.get())
                                : new (Ctx) NullStmt(Loc));
      P.ExitScope();
      Interp.cppshAddBuilt(Stmt);
    }
  }
  return cppshEndBuildAndExecute();
}

namespace {
// What staging changes while compiling for a frame, put back after -- and
// what the top-level declaration being staged around it has set (a staged
// call hoisted out of `x = f();` runs f, whose staged code is compiled here):
// none of it the units built for the frame's (each would be taken back as
// that declaration is, IncrementalParser::FinishPTU).
struct CppshFrameState {
  bool WasHoist = std::exchange(CppshInHoist, false);
  CppshStagingScope Staging;
  ~CppshFrameState() { CppshInHoist = WasHoist; }
};
} // namespace

// ---- Staged statements (cppsh) --------------------------------------------

// A function defined from the AST, at the translation unit: Name(ParamTypes)
// returning Ret, its body what MakeBody makes in its scope.
static FunctionDecl *cppshDefineFunction(
    Sema &S, llvm::StringRef Name, QualType Ret, ArrayRef<QualType> ParamTypes,
    llvm::function_ref<Stmt *(FunctionDecl *, ArrayRef<ParmVarDecl *>)> MakeBody) {
  ASTContext &Ctx = S.Context;
  IdentifierTable &Idents = S.getPreprocessor().getIdentifierTable();
  const SourceLocation Loc;
  QualType FnTy =
      Ctx.getFunctionType(Ret, ParamTypes, FunctionProtoType::ExtProtoInfo());
  auto *FD = FunctionDecl::Create(Ctx, Ctx.getTranslationUnitDecl(), Loc, Loc,
                                  DeclarationName(&Idents.get(Name)), FnTy,
                                  Ctx.getTrivialTypeSourceInfo(FnTy, Loc),
                                  SC_None);
  SmallVector<ParmVarDecl *, 4> Params;
  for (unsigned I = 0; I < ParamTypes.size(); ++I) {
    auto *P = ParmVarDecl::Create(
        Ctx, FD, Loc, Loc, &Idents.get("__cppsh_p" + std::to_string(I)),
        ParamTypes[I], Ctx.getTrivialTypeSourceInfo(ParamTypes[I], Loc), SC_None,
        /*DefArg=*/nullptr);
    P->setScopeInfo(0, I);
    Params.push_back(P);
  }
  FD->setParams(Params);
  Stmt *Body = nullptr;
  {
    Sema::SynthesizedFunctionScope Scope(S, FD);
    Body = MakeBody(FD, Params);
    // A coroutine (its body co_awaits, co_returns): its body completed as
    // one -- the promise, the suspends around it.
    if (Body && S.getCurFunction() && S.getCurFunction()->isCoroutine())
      S.CheckCompletedCoroutineBody(FD, Body);
    // An `auto` function that returns nothing returns void.
    if (Body && FD->getReturnType()->isUndeducedType())
      if (AutoType *AT = FD->getReturnType()->getContainedAutoType())
        S.DeduceFunctionTypeFromReturnExpr(FD, Loc, /*RetExpr=*/nullptr, AT);
    if (Body)
      FD->setBody(Body);
  }
  if (!Body || FD->getReturnType()->isUndeducedType())
    return nullptr;
  Ctx.getTranslationUnitDecl()->addDecl(FD);
  return FD;
}

// `*(T *)E[I]`, E a `void **`: the object a frame entry points to.
static Expr *cppshFrameEntry(Sema &S, ParmVarDecl *Frame, unsigned I,
                             QualType PtrTy) {
  ASTContext &Ctx = S.Context;
  const SourceLocation Loc;
  ExprResult Base = S.DefaultLvalueConversion(
      S.BuildDeclRefExpr(Frame, Frame->getType(), VK_LValue, Loc));
  if (!Base.isUsable())
    return nullptr;
  Expr *Index = IntegerLiteral::Create(
      Ctx, llvm::APInt(Ctx.getIntWidth(Ctx.IntTy), I), Ctx.IntTy, Loc);
  ExprResult Entry = S.CreateBuiltinArraySubscriptExpr(Base.get(), Loc, Index, Loc);
  if (!Entry.isUsable())
    return nullptr;
  ExprResult Ptr = S.BuildCStyleCastExpr(
      Loc, Ctx.getTrivialTypeSourceInfo(PtrTy, Loc), Loc, Entry.get());
  return Ptr.isUsable() ? Ptr.get() : nullptr;
}

// The snapshot of the object of type T at P (std::sh::__cppsh_snapshot),
// taken now -- through a function compiled once for each type.
static bool cppshSnapshotAt(Interpreter &Interp, Sema &S, QualType T,
                            const void *P) {
  using SnapFn = void (*)(void **);
  static llvm::DenseMap<const Type *, SnapFn> Snappers;
  static unsigned Count = 0;
  ASTContext &Ctx = S.Context;
  T = Ctx.getCanonicalType(T).getUnqualifiedType();
  SnapFn Fn = Snappers.lookup(T.getTypePtr());
  if (!Fn) {
    ExprResult Snap = cppshShCallee(S, "__cppsh_snapshot");
    if (!Snap.isUsable() || !cppshReport(Interp.cppshBeginBuild()))
      return false;
    const QualType VoidPtrPtr = Ctx.getPointerType(Ctx.VoidPtrTy);
    FunctionDecl *FD = cppshDefineFunction(
        S, "__cppsh_snap" + std::to_string(Count++), Ctx.VoidTy, {VoidPtrPtr},
        [&](FunctionDecl *, ArrayRef<ParmVarDecl *> Ps) -> Stmt * {
          const SourceLocation Loc;
          Expr *Ptr = cppshFrameEntry(S, Ps[0], 0, Ctx.getPointerType(T));
          ExprResult Obj = Ptr ? S.CreateBuiltinUnaryOp(Loc, UO_Deref, Ptr)
                               : ExprError();
          Expr *Arg = Obj.isUsable() ? Obj.get() : nullptr;
          ExprResult Call = Arg ? S.BuildCallExpr(S.TUScope, Snap.get(), Loc,
                                                  Arg, Loc)
                                : ExprError();
          ExprResult Full =
              Call.isUsable()
                  ? S.ActOnFinishFullExpr(Call.get(), /*DiscardedValue=*/true)
                  : ExprError();
          if (!Full.isUsable())
            return nullptr;
          Stmt *Stmts[1] = {Full.get()};
          return CompoundStmt::Create(Ctx, Stmts, FPOptionsOverride(), Loc, Loc);
        });
    if (FD)
      Interp.cppshAddBuilt(FD);
    if (!cppshReport(Interp.cppshEndBuildAndExecute()) || !FD)
      return false;
    llvm::Expected<llvm::orc::ExecutorAddr> Addr =
        Interp.getSymbolAddress(GlobalDecl(FD));
    if (!Addr) {
      llvm::consumeError(Addr.takeError());
      return false;
    }
    Fn = Addr->toPtr<SnapFn>();
    Snappers[T.getTypePtr()] = Fn;
  }
  void *Entries[1] = {const_cast<void *>(P)};
  Fn(Entries);
  return true;
}

// The expression rebuilding the value of the object of type T at Object:
// a C string's literal; else rebuilt from the object's snapshot.
static Expr *cppshRebuildAt(Sema &S, QualType T, const void *Object,
                            SourceLocation Loc) {
  if (!CppshActiveInterpreter || !Object)
    return nullptr;
  ASTContext &Ctx = S.Context;
  if (const auto *PT = T->getAs<PointerType>();
      PT && PT->getPointeeType()->isCharType()) {
    const char *Str = *static_cast<const char *const *>(Object);
    if (!Str)
      return nullptr;
    llvm::StringRef Text(Str, ::strnlen(Str, 1 << 16));
    QualType Char = Ctx.CharTy.withConst();
    Expr *Lit = StringLiteral::Create(
        Ctx, Text, StringLiteralKind::Ordinary, /*Pascal=*/false,
        Ctx.getStringLiteralArrayType(Ctx.CharTy, Text.size()), Loc);
    return S.ImpCastExprToType(Lit, Ctx.getPointerType(Char), CK_ArrayToPointerDecay)
        .get();
  }
  llvm::Expected<llvm::orc::ExecutorAddr> Reader =
      CppshActiveInterpreter->getSymbolAddressFromLinkerName("__cppsh_snapshot_of");
  if (!Reader) {
    llvm::consumeError(Reader.takeError());
    return nullptr;
  }
  using ReaderFn = const char *(*)(const void *, unsigned long long *);
  unsigned long long Size = 0;
  const char *Data = Reader->toPtr<ReaderFn>()(Object, &Size);
  if (!Data)
    return nullptr;
  CppshSnapshot R{reinterpret_cast<const unsigned char *>(Data),
                  reinterpret_cast<const unsigned char *>(Data) + Size};
  return cppshRebuild(S, T, R, Loc);
}

namespace {
// A staged statement's instantiation for one set of values: its function.
struct CppshStagedCompiled {
  // The locals whose values it was compiled with -- those its instantiation
  // wanted constant -- and those values; the staged result's type.
  SmallVector<unsigned, 4> Wanted;
  SmallVector<llvm::FoldingSetNodeID, 4> Profiles;
  SmallVector<QualType, 2> Input;
  FunctionDecl *Function = nullptr;
  void *Address = nullptr;
  // A staged function's rest: the type of the result its returns give.
  QualType Result;
};
// The code compiled for each staged statement, by the values it was compiled
// for (cppshRunStaged).
std::map<const CppshStagedStmt *, std::vector<CppshStagedCompiled>> CppshCompiled;
// A local's value as staged code is compiled with it: read from memory
// (plain data) or rebuilt from its snapshot; its profile, for finding the
// instantiation compiled with it again.
struct CppshBound {
  bool Done = false;
  std::optional<APValue> Value;
  Expr *Rebuild = nullptr;
  llvm::FoldingSetNodeID Profile;
};
// Each time a staged function's result is kept: so that a staged statement
// whose body left by a return knows whether code staged inside it kept one.
unsigned CppshKeptResults = 0;

// cppsh: a quiet attempt's diagnostics: counted, not shown -- the first
// error's text kept (its location, its message), for the trace.
namespace {
struct CppshQuietConsumer : DiagnosticConsumer {
  std::string First;
  void HandleDiagnostic(DiagnosticsEngine::Level Level,
                        const Diagnostic &Info) override {
    DiagnosticConsumer::HandleDiagnostic(Level, Info);
    if (Level < DiagnosticsEngine::Error || !First.empty())
      return;
    SmallString<128> Message;
    Info.FormatDiagnostic(Message);
    if (Info.hasSourceManager() && Info.getLocation().isValid())
      First = Info.getLocation().printToString(Info.getSourceManager()) + ": ";
    First += Message.str();
  }
};
} // namespace
} // namespace

// A staged statement, reached as its function runs (CodeGen's
// EmitCppshStagedStmt): its body instantiated for the values its frame
// holds now -- each local's that the body does not change, read from memory
// (or rebuilt from its snapshot), a constant of what is compiled -- into a
// function of its own, taking the frame and where the function around the
// statement returns its value, and run. One instantiation for each set of
// values, found again for the same values. What it returns: how the body
// left (0: off its end; 1, 2: by a break, a continue; 3: by a return, its
// value constructed; 4 + I: by a goto to its I-th label outside it). The rest
// of a staged function's body (keepsResult): what it returns constructed in
// storage of its type made for it, named by a global, __cppsh_resK, kept for
// the function's caller.
// The runs prepared (__cppsh_staged_prepare) whose code the JIT's own code
// is calling: what follows each call (__cppsh_staged_done) by them. One that
// threw is left behind, dropped by the next done of a run around it.
struct CppshRunInFlight {
  const CppshStagedStmt *Staged = nullptr;
  bool Keep = false;
  std::string ResultName;
  unsigned KeptBefore = 0;
  int Entry = 0;
};
static thread_local std::vector<CppshRunInFlight> CppshRunsInFlight;
// The interpreter -- its Sema, its JIT, the staging's state -- used by one
// thread at a time: staged code reached on two threads at once is compiled
// one after the other (what is compiled may run code reaching staged code
// again on the same thread: recursive). The staged code itself runs outside
// it, called by the code that reached it.
static std::recursive_mutex CppshInterpreterLock;

// The code each staged statement was last reached and run with, and the
// bytes of the locals it was compiled for: where they are the same again,
// that code at once, nothing else looked at (__cppsh_staged_prepare) -- the
// cost of reaching compiled staged code a lock and a comparison. Only code
// keeping no result and using no staged call's: its frame then the one it is
// handed, as it is; and only locals of plain data.
struct CppshLastRun {
  void *Address = nullptr;
  SmallVector<std::pair<unsigned, std::string>, 4> Bytes;
};
static llvm::DenseMap<const CppshStagedStmt *, CppshLastRun> CppshLastRuns;

static int cppshRunStaged(const CppshStagedStmt *Staged, void *const *Frame,
                          void *Slot, int Entry, void *OuterPromise = nullptr,
                          void **HandleOut = nullptr, void **FnOut = nullptr,
                          void **SlotOut = nullptr) {
  // Code that suspends the coroutine it is in: compiled as a coroutine, its
  // handle handed back (HandleOut), not run here.
  const bool Coro = HandleOut != nullptr;
  if (!CppshActiveInterpreter || !Staged || !Staged->getStagedDecl())
    return 0;
  Interpreter &Interp = *CppshActiveInterpreter;
  Sema &S = Interp.getCompilerInstance()->getSema();
  ASTContext &Ctx = S.Context;
  IdentifierTable &Idents = S.getPreprocessor().getIdentifierTable();
  const SourceLocation Loc;
  auto Fail = [](llvm::StringRef Why) {
    llvm::errs() << "error: cppsh: a staged statement cannot run: " << Why << "\n";
    return 0;
  };
  auto *SS = const_cast<CppshStagedStmt *>(Staged);
  if (cppshTraceStaging())
    llvm::errs() << "cppsh-trace: running staged "
                 << SS->getBeginLoc().printToString(S.getSourceManager())
                 << " entry " << Entry << "\n";
  CppshStagedDecl *SD = SS->getStagedDecl();
  ArrayRef<ImplicitParamDecl *> Params = SD->parameters();
  const unsigned N = Params.size();
  if (SS->getNumFrame() != N + (SD->usesThis() ? 1 : 0))
    return Fail("its frame does not match it");
  const bool Keep = SS->keepsResult();
  CppshFrameState State;

  // Each entry's type and object; the staged result's, the last result kept.
  SmallVector<QualType, 8> Types;
  SmallVector<void *, 8> Objects(Frame, Frame + N);
  SmallVector<QualType, 2> ResultTypes;
  const size_t NumResults = SD->resultTypeParms().size();
  if (NumResults > N || NumResults > CppshResultHistory.size())
    return Fail("the staged calls it uses left no results");
  for (unsigned I = 0; I < N; ++I) {
    QualType T = Params[I]->getType().getNonReferenceType();
    if (I + NumResults >= N && T->isDependentType()) {
      // The result of the J-th staged call of the K it uses: the K-J-th kept
      // last.
      const std::string &Name =
          CppshResultHistory[CppshResultHistory.size() - NumResults +
                             (I - (N - NumResults))];
      LookupResult R(S, &Idents.get(Name), Loc, Sema::LookupOrdinaryName);
      auto *Result = !Name.empty() &&
                             S.LookupQualifiedName(R, Ctx.getTranslationUnitDecl())
                         ? R.getAsSingle<VarDecl>()
                         : nullptr;
      if (!Result)
        return Fail("the staged call it uses left no result");
      llvm::Expected<llvm::orc::ExecutorAddr> Addr =
          Interp.getSymbolAddress(GlobalDecl(Result));
      if (!Addr) {
        llvm::consumeError(Addr.takeError());
        return Fail("the staged call's result is not found");
      }
      T = Result->getType().getNonReferenceType();
      ResultTypes.push_back(T);
      Objects[I] = Addr->toPtr<void *>();
      // A reference naming the storage the result was constructed in (a
      // staged function's kept result): that storage.
      if (Result->getType()->isReferenceType())
        Objects[I] = *static_cast<void **>(Objects[I]);
    }
    if (T->isDependentType())
      return Fail("a type of its frame is not known");
    Types.push_back(T);
  }

  // The values it may be compiled with: each local's, made only where an
  // instantiation wants it constant -- one the body changes never (it is no
  // constant there).
  Stmt *Body = SS->getBody();
  SmallVector<CppshBound, 8> Bounds(N);
  auto ValueOf = [&](unsigned I) -> CppshBound & {
    CppshBound &B = Bounds[I];
    if (B.Done)
      return B;
    B.Done = true;
    const QualType T = Types[I];
    if (!Objects[I] || T->isIncompleteType() || cppshMutates(Body, Params[I])) {
      B.Profile.AddInteger(0u);
      return B;
    }
    if (T.isTriviallyCopyableType(Ctx))
      B.Value = cppshValueAt(Ctx, T, static_cast<const unsigned char *>(Objects[I]));
    if (cppshTraceStaging())
      llvm::errs() << "cppsh-trace: value of " << Params[I]->getName() << " (slot "
                   << I << ", " << T.getAsString() << " at " << Objects[I] << "): "
                   << (B.Value ? B.Value->getAsString(Ctx, T) : std::string("none"))
                   << "\n";
    if (B.Value) {
      B.Profile.AddInteger(1u);
      B.Value->Profile(B.Profile);
      return B;
    }
    // Not plain data: rebuilt from the snapshot taken of it now.
    if (!T->getAs<PointerType>())
      cppshSnapshotAt(Interp, S, T, Objects[I]);
    B.Rebuild = cppshRebuildAt(S, T, Objects[I], Params[I]->getLocation());
    if (B.Rebuild) {
      B.Profile.AddInteger(2u);
      B.Rebuild->Profile(B.Profile, Ctx, /*Canonical=*/true);
    } else {
      B.Profile.AddInteger(0u);
    }
    return B;
  };

  // An instantiation compiled with the values the locals it wanted have now.
  std::map<const CppshStagedStmt *, std::vector<CppshStagedCompiled>> &Compiled =
      CppshCompiled;
  static unsigned Count = 0;
  std::vector<CppshStagedCompiled> &Instances = Compiled[Staged];
  SmallVector<QualType, 2> Input;
  for (QualType RT : ResultTypes)
    Input.push_back(Ctx.getCanonicalType(RT));
  CppshStagedCompiled *Found = nullptr;
  for (CppshStagedCompiled &C : Instances) {
    if (C.Input != Input)
      continue;
    bool Same = true;
    for (unsigned K = 0; K < C.Wanted.size() && Same; ++K)
      Same = ValueOf(C.Wanted[K]).Profile == C.Profiles[K];
    if (Same) {
      Found = &C;
      break;
    }
  }

  // The function around the statement: where its returns go, whose access
  // and `this` it has.
  DeclContext *Around =
      SD->getDeclContext()->getEnclosingNonExpansionStatementContext();
  auto *Outer = dyn_cast<FunctionDecl>(Around);

  const bool WasNeeded = std::exchange(CppshCutNeeded, false);
  auto RestoreNeeded = llvm::scope_exit([&] { CppshCutNeeded = WasNeeded; });
  // Compiled for these values: `int __cppsh_stagedK(void **frame, void
  // *slot, int entry)`, its body the statement's instantiated -- first with
  // no value bound; each local whose value an instantiation wanted constant
  // bound in the next, until none more is wanted (those attempts quiet, what
  // they queued dropped); a failure with nothing more wanted reported.
  if (!Found) {
    const QualType VoidPtrPtr = Ctx.getPointerType(Ctx.VoidPtrTy);
    // The interpreter's value printing, for a body whose last statement's
    // value is shown.
    auto PrintValueFn = [&](Expr *E) -> Expr * {
      llvm::Expected<Expr *> Shown = Interp.cppshPrintValue(E);
      if (!Shown) {
        llvm::consumeError(Shown.takeError());
        return nullptr;
      }
      return *Shown;
    };
    llvm::function_ref<Expr *(Expr *)> PrintValue = PrintValueFn;
    // What it wanted the times before, wanted from the start: the same code
    // wants the same locals, whatever their values -- no attempt made only
    // to learn that again.
    SmallVector<unsigned, 4> Want;
    for (const CppshStagedCompiled &C : Instances)
      for (unsigned I : C.Wanted)
        if (I < N && !llvm::is_contained(Want, I))
          Want.push_back(I);
    FunctionDecl *F = nullptr;
    QualType KeptType;
    for (bool Report = false;;) {
      if (!cppshReport(Interp.cppshBeginBuild()))
        return Fail("no unit to compile it in");
      // A quiet attempt: its diagnostics counted (an error fails it), not
      // shown -- the first error kept, for the trace. Every attempt with its
      // diagnostics live: no hold of a statement's left over (the reporting
      // one would show nothing), none suppressed.
      DiagnosticsEngine &Diags = S.getDiagnostics();
      cppshEndNeedDiagnostics(S);
      const bool WasSuppressed = Diags.getSuppressAllDiagnostics();
      Diags.setSuppressAllDiagnostics(false);
      auto RestoreSuppressed = llvm::scope_exit(
          [&] { Diags.setSuppressAllDiagnostics(WasSuppressed); });
      CppshQuietConsumer Quiet;
      DiagnosticConsumer *const Client = Diags.getClient();
      const bool OwnsClient = Diags.ownsClient();
      std::unique_ptr<DiagnosticConsumer> OwnedClient;
      if (!Report) {
        OwnedClient = Diags.takeClient();
        Diags.setClient(&Quiet, /*ShouldOwnClient=*/false);
      }
      const size_t PendingBefore = S.PendingInstantiations.size();
      const size_t LocalPendingBefore = S.PendingLocalImplicitInstantiations.size();
      const size_t SpecsBefore = cppshSpecializationMark();
      const size_t UndefinedBefore = S.UndefinedButUsed.size();
      llvm::DenseMap<const VarDecl *, unsigned> IndexOf;
      CppshStagedWanted.clear();
      Sema::CppshStagedRun Run;
      Run.KeepsResult = Keep;
      Run.ReturnType =
          Keep ? QualType() : Outer ? Outer->getReturnType() : Ctx.VoidTy;
      Run.AccessContext = Around;
      Run.Staged = SS;
      Run.Coroutine = Coro;
      // A coroutine's: std::sh::__cppsh_staged_coro<P>, P the outer
      // coroutine's promise, taking that promise.
      QualType FnResult = Ctx.IntTy;
      QualType SecondParam = Ctx.VoidPtrTy;
      if (Coro) {
        auto *CoroBody =
            dyn_cast_or_null<CoroutineBodyStmt>(Outer ? Outer->getBody() : nullptr);
        if (!CoroBody || !CoroBody->getPromiseDecl())
          return Fail("the coroutine it is in has no promise");
        const QualType PromiseT = CoroBody->getPromiseDecl()->getType();
        NamespaceDecl *Std = S.getStdNamespace();
        LookupResult ShR(S, &Idents.get("sh"), Loc, Sema::LookupNamespaceName);
        if (Std)
          S.LookupQualifiedName(ShR, Std);
        auto *Sh = ShR.getAsSingle<NamespaceDecl>();
        LookupResult CoroR(S, &Idents.get("__cppsh_staged_coro"), Loc,
                           Sema::LookupOrdinaryName);
        if (Sh)
          S.LookupQualifiedName(CoroR, Sh);
        ClassTemplateDecl *CoroT = nullptr;
        for (NamedDecl *D : CoroR)
          if (auto *CTD = dyn_cast<ClassTemplateDecl>(D->getUnderlyingDecl()))
            CoroT = CTD;
        if (!CoroT)
          return Fail("std::sh::__cppsh_staged_coro is not found");
        TemplateArgumentListInfo Args(Loc, Loc);
        Args.addArgument(TemplateArgumentLoc(
            TemplateArgument(PromiseT), Ctx.getTrivialTypeSourceInfo(PromiseT, Loc)));
        FnResult = S.CheckTemplateIdType(ElaboratedTypeKeyword::None,
                                         TemplateName(CoroT), Loc, Args, nullptr,
                                         /*ForNestedNameSpecifier=*/false);
        if (FnResult.isNull())
          return Fail("std::sh::__cppsh_staged_coro is not usable");
        SecondParam = Ctx.getPointerType(PromiseT);
      }
      F = cppshDefineFunction(
          S, "__cppsh_staged" + std::to_string(Count++), FnResult,
          {VoidPtrPtr, SecondParam, Ctx.IntTy},
          [&](FunctionDecl *Fn, ArrayRef<ParmVarDecl *> Ps) -> Stmt * {
            Run.Function = Fn;
            Run.Slot = Coro ? nullptr : Ps[1];
            Run.OuterPromise = Coro ? Ps[1] : nullptr;
            Run.Entry = Ps[2];
            Run.PrintValue = PrintValue;
            // Known to code generation: staged code inside it leaves through
            // it, and returns its value where its slot points.
            Fn->addAttr(AnnotateAttr::CreateImplicit(Ctx, "cppsh.staged.run",
                                                     nullptr, 0, SourceRange()));
            // An inline function (kept: used): a static local of its code,
            // and its guard, shared by every function its code is compiled
            // into (Sema::CppshStagedStatics), as the linker merges them.
            Fn->setInlineSpecified(true);
            Fn->addAttr(UsedAttr::CreateImplicit(Ctx));
            SmallVector<Stmt *, 16> Stmts;
            SmallVector<VarDecl *, 8> Locals;
            // Each local: `T &name = *(T *)frame[I];` -- its value bound
            // where it is wanted.
            for (unsigned I = 0; I < N; ++I) {
              const QualType RefT = Ctx.getLValueReferenceType(Types[I]);
              auto *L = VarDecl::Create(Ctx, Fn, Loc, Params[I]->getLocation(),
                                        Params[I]->getIdentifier(), RefT,
                                        Ctx.getTrivialTypeSourceInfo(RefT, Loc),
                                        SC_None);
              Expr *Ptr =
                  cppshFrameEntry(S, Ps[0], I, Ctx.getPointerType(Types[I]));
              ExprResult Obj =
                  Ptr ? S.CreateBuiltinUnaryOp(Loc, UO_Deref, Ptr) : ExprError();
              if (!Obj.isUsable())
                return nullptr;
              S.AddInitializerToDecl(L, Obj.get(), /*DirectInit=*/false);
              if (L->isInvalidDecl())
                return nullptr;
              CppshStagedTracked.insert(L);
              IndexOf[L] = I;
              if (llvm::is_contained(Want, I)) {
                CppshBound &B = ValueOf(I);
                if (B.Value)
                  CppshParamValue[L] = *B.Value;
                else if (B.Rebuild)
                  CppshParamRebuild[L] = B.Rebuild;
              }
              StmtResult DS =
                  S.ActOnDeclStmt(S.ConvertDeclToDeclGroup(L), Loc, Loc);
              if (!DS.isUsable())
                return nullptr;
              Stmts.push_back(DS.get());
              Locals.push_back(L);
            }
            // `this`: `C *__cppsh_this = (C *)frame[N];`.
            if (SD->usesThis()) {
              const QualType ThisTy = SS->frame().back()->getType();
              auto *This = VarDecl::Create(
                  Ctx, Fn, Loc, Loc, &Idents.get("__cppsh_this"), ThisTy,
                  Ctx.getTrivialTypeSourceInfo(ThisTy, Loc), SC_None);
              Expr *Ptr = cppshFrameEntry(S, Ps[0], N, ThisTy);
              if (!Ptr)
                return nullptr;
              S.AddInitializerToDecl(This, Ptr, /*DirectInit=*/false);
              StmtResult DS =
                  S.ActOnDeclStmt(S.ConvertDeclToDeclGroup(This), Loc, Loc);
              if (!DS.isUsable())
                return nullptr;
              Stmts.push_back(DS.get());
              Run.This = This;
            }
            // The values bound live while the body is instantiated: what
            // Sema needs constant -- not as code is generated.
            const bool WasLive = std::exchange(CppshStagedLive, true);
            const unsigned ErrorsBefore = Diags.getNumErrors();
            StmtResult Inst =
                S.InstantiateCppshStaged(SS, Locals, ResultTypes, Run);
            CppshStagedLive = WasLive;
            cppshEndNeedDiagnostics(S);
            if (!Inst.isUsable() || Diags.getNumErrors() != ErrorsBefore)
              return nullptr;
            Stmts.push_back(Inst.get());
            Expr *Zero = IntegerLiteral::Create(
                Ctx, llvm::APInt(Ctx.getIntWidth(Ctx.IntTy), 0), Ctx.IntTy, Loc);
            if (Coro) {
              StmtResult Done = S.BuildCoreturnStmt(Loc, Zero, /*IsImplicit=*/true);
              if (!Done.isUsable())
                return nullptr;
              Stmts.push_back(Done.get());
            } else {
              Stmts.push_back(ReturnStmt::Create(Ctx, Loc, Zero, nullptr));
            }
            return CompoundStmt::Create(Ctx, Stmts, FPOptionsOverride(), Loc, Loc);
          });
      if (!Report) {
        if (OwnsClient)
          Diags.setClient(OwnedClient.release(), /*ShouldOwnClient=*/true);
        else
          Diags.setClient(Client, /*ShouldOwnClient=*/false);
      }
      // What it wanted that was not bound: bound next time.
      bool More = false;
      for (const VarDecl *VD : CppshStagedWanted)
        if (auto It = IndexOf.find(VD);
            It != IndexOf.end() && !llvm::is_contained(Want, It->second)) {
          Want.push_back(It->second);
          More = true;
        }
      if (!F && !Report && cppshTraceStaging()) {
        llvm::errs() << "cppsh-trace: attempt at "
                     << SS->getBeginLoc().printToString(S.getSourceManager())
                     << " failed: "
                     << (Quiet.First.empty() ? std::string("no error")
                                             : Quiet.First)
                     << "; wanted:";
        for (const VarDecl *VD : CppshStagedWanted)
          llvm::errs() << " " << VD->getName();
        llvm::errs() << "\n";
        // The body it instantiated, as it stands (an outer staged
        // statement's instantiation made it, where it is nested).
        if (::getenv("CPPSH_TRACE_STAGING_BODY")) {
          llvm::errs() << "cppsh-trace: its body: ";
          SS->getBody()->printPretty(llvm::errs(), nullptr,
                                     PrintingPolicy(Ctx.getLangOpts()));
          llvm::errs() << "\n";
        }
      }
      // Compiled, but having wanted a value it was not given (a placeholder
      // stood in for it): not the code for these values -- again, with it.
      if (F && More && !Report)
        F = nullptr;
      if (F) {
        Interp.cppshAddBuilt(F);
        KeptType = Run.ReturnType;
        if (!cppshReport(Interp.cppshEndBuildAndExecute()))
          return Fail("it did not compile for the values it runs with");
        break;
      }
      // Not compiled: what it queued for instantiation dropped (each function
      // so dropped queued again by its next use), the unit ended empty; the
      // specializations on argument values it made forgotten.
      cppshForgetSpecializationsSince(SpecsBefore);
      // And what only it used, not defined: no warning of it.
      while (S.UndefinedButUsed.size() > UndefinedBefore)
        S.UndefinedButUsed.pop_back();
      for (size_t I = PendingBefore; I < S.PendingInstantiations.size(); ++I)
        if (auto *FD = dyn_cast_or_null<FunctionDecl>(S.PendingInstantiations[I].first);
            FD && !FD->isDefined()) {
          if (FunctionTemplateSpecializationInfo *Info =
                  FD->getTemplateSpecializationInfo())
            Info->setPointOfInstantiation(SourceLocation());
          else if (MemberSpecializationInfo *MSI = FD->getMemberSpecializationInfo())
            MSI->setPointOfInstantiation(SourceLocation());
        }
      if (S.PendingInstantiations.size() > PendingBefore)
        S.PendingInstantiations.resize(PendingBefore);
      if (S.PendingLocalImplicitInstantiations.size() > LocalPendingBefore)
        S.PendingLocalImplicitInstantiations.resize(LocalPendingBefore);
      llvm::consumeError(Interp.cppshEndBuildAndExecute());
      if (Report)
        return Fail("it did not compile for the values it runs with");
      // Nothing more to bind: the failure is the code's -- reported.
      if (!More)
        Report = true;
    }
    llvm::Expected<llvm::orc::ExecutorAddr> Addr =
        Interp.getSymbolAddress(GlobalDecl(F));
    if (!Addr) {
      llvm::consumeError(Addr.takeError());
      return Fail("its compiled function is not found");
    }
    CppshStagedCompiled C;
    C.Wanted = Want;
    for (unsigned I : Want)
      C.Profiles.push_back(ValueOf(I).Profile);
    C.Input = Input;
    C.Function = F;
    C.Address = Addr->toPtr<void *>();
    C.Result = KeptType;
    Instances.push_back(std::move(C));
    Found = &Instances.back();
    // Compiled for many values (a loop whose staged statement each
    // iteration reaches with a new one): said, as each new value compiles
    // again -- what makes it slow, and where.
    if (const size_t Count = Instances.size();
        Count == 16 || Count == 128 || Count == 1024)
      llvm::errs() << "warning: cppsh: staged code at "
                   << SS->getBeginLoc().printToString(S.getSourceManager())
                   << " has been compiled for " << Count
                   << " different values; each new value compiles it again\n";
  }
  if (!Found->Address)
    return Fail("its compiled function is not found");
  if (!Found->Address)
    return Fail("its compiled function is not found");

  // A staged function's rest: storage of its result's type, named by a
  // global (`T &__cppsh_resK = *(T *)storage;`) -- what its return
  // constructs is kept there, for the function's caller.
  std::string ResultName;
  if (Keep && !Found->Result.isNull() && !Found->Result->isVoidType()) {
    const QualType T = Found->Result;
    const CharUnits Size = Ctx.getTypeSizeInChars(T);
    const CharUnits Align = Ctx.getTypeAlignInChars(T);
    Slot = ::operator new(std::max<size_t>(Size.getQuantity(), 1),
                          std::align_val_t(Align.getQuantity()));
    if (!cppshReport(Interp.cppshBeginBuild()))
      return Fail("no unit to keep its result in");
    ResultName = "__cppsh_res" + std::to_string(CppshContinuations++);
    const QualType RefT = Ctx.getLValueReferenceType(T);
    auto *Res = VarDecl::Create(Ctx, Ctx.getTranslationUnitDecl(), Loc, Loc,
                                &Idents.get(ResultName), RefT,
                                Ctx.getTrivialTypeSourceInfo(RefT, Loc), SC_None);
    Expr *Int = IntegerLiteral::Create(
        Ctx, llvm::APInt(64, llvm::bit_cast<uintptr_t>(Slot)),
        Ctx.UnsignedLongLongTy, Loc);
    ExprResult Ptr = S.BuildCStyleCastExpr(
        Loc, Ctx.getTrivialTypeSourceInfo(Ctx.getPointerType(T), Loc), Loc, Int);
    ExprResult Obj = Ptr.isUsable() ? S.CreateBuiltinUnaryOp(Loc, UO_Deref, Ptr.get())
                                    : ExprError();
    if (Obj.isUsable()) {
      S.AddInitializerToDecl(Res, Obj.get(), /*DirectInit=*/false);
      S.FinalizeDeclaration(Res);
      S.PushOnScopeChains(Res, S.TUScope);
      Interp.cppshAddBuilt(Res);
    }
    if (!cppshReport(Interp.cppshEndBuildAndExecute()) || !Obj.isUsable())
      return Fail("its result could not be kept");
  } else if (Keep) {
    Slot = nullptr;
  }

  // The frame, with the staged result's object in its place.
  SmallVector<void *, 8> Entries(Objects.begin(), Objects.end());
  if (SD->usesThis())
    Entries.push_back(Frame[N]);
  Entries.push_back(nullptr);
  // A coroutine's: run later -- the outer coroutine's frame array (its own
  // object, living as long as it does), updated in place.
  if (Coro) {
    auto *OuterFrame = const_cast<void **>(Frame);
    for (unsigned I = 0; I < Entries.size(); ++I)
      OuterFrame[I] = Entries[I];
    using CoroFn = void *(*)(void *const *, void *, int);
    *HandleOut = reinterpret_cast<CoroFn>(Found->Address)(Frame, OuterPromise, Entry);
    return 0;
  }
  // Called by the code that reached it (FnOut): the frame updated in place,
  // the function and its slot handed back -- no frame of the interpreter's
  // between that code and what it runs, an exception thrown there unwinding
  // through the JIT's code alone. What follows the call: __cppsh_staged_done.
  if (FnOut) {
    auto *OuterFrame = const_cast<void **>(Frame);
    for (unsigned I = 0; I < Entries.size(); ++I)
      OuterFrame[I] = Entries[I];
    *FnOut = Found->Address;
    *SlotOut = Slot;
    CppshRunsInFlight.push_back({SS, Keep, ResultName, CppshKeptResults, Entry});
    // Remembered for the next time, where it can be.
    CppshLastRun Last;
    Last.Address = Found->Address;
    bool Plain = !Keep && SD->resultTypeParms().empty();
    for (unsigned I : Found->Wanted) {
      if (!Plain)
        break;
      if (I >= N || !Objects[I] || !Types[I].isTriviallyCopyableType(Ctx)) {
        Plain = false;
        break;
      }
      const size_t Size = Ctx.getTypeSizeInChars(Types[I]).getQuantity();
      Last.Bytes.push_back(
          {I, std::string(static_cast<const char *>(Objects[I]), Size)});
    }
    if (Plain)
      CppshLastRuns[SS] = std::move(Last);
    else
      CppshLastRuns.erase(SS);
    return 0;
  }
  using StagedFn = int (*)(void **, void *, int);
  const unsigned KeptBefore = CppshKeptResults;
  const int Left =
      reinterpret_cast<StagedFn>(Found->Address)(Entries.data(), Slot, Entry);
  if (cppshTraceStaging())
    llvm::errs() << "cppsh-trace: ran staged "
                 << SS->getBeginLoc().printToString(S.getSourceManager())
                 << " entry " << Entry << " left " << Left
                 << (Keep ? (ResultName.empty() ? " keeping nothing"
                                                : " keeping " + ResultName)
                          : std::string())
                 << "\n";
  // Its return kept the result -- unless code staged inside it did (that
  // code's result kept already).
  if (Keep && Left == 3 && !ResultName.empty() && CppshKeptResults == KeptBefore) {
    CppshLastResult = ResultName;
    CppshResultHistory.push_back(ResultName);
    ++CppshKeptResults;
  }
  return Left;
}

// The coroutine of staged code that suspends the coroutine it is in
// (std::sh::__cppsh_staged_step): its handle, not started.
extern "C" void *__cppsh_staged_coro_start(const void *Node, void *const *Frame,
                                           void *OuterPromise, int Entry) {
  if (!CppshActiveInterpreter)
    return nullptr;
  std::lock_guard<std::recursive_mutex> Lock(CppshInterpreterLock);
  void *Handle = nullptr;
  cppshRunStaged(static_cast<const CppshStagedStmt *>(Node), Frame, nullptr,
                 Entry, OuterPromise, &Handle);
  return Handle;
}

// The code compiled for a staged statement and these values, for the code
// that reached it to call (`fn(frame, *slot_out, entry)`); null where it
// cannot be compiled (said so).
extern "C" void *__cppsh_staged_prepare(const void *Node, void *const *Frame,
                                        void *Slot, int Entry, void **SlotOut) {
  if (!CppshActiveInterpreter) {
    llvm::errs() << "error: cppsh: a staged statement cannot run: no interpreter\n";
    return nullptr;
  }
  std::lock_guard<std::recursive_mutex> Lock(CppshInterpreterLock);
  // Reached with the values it was last run with: that code.
  if (auto It = CppshLastRuns.find(static_cast<const CppshStagedStmt *>(Node));
      It != CppshLastRuns.end() &&
      llvm::all_of(It->second.Bytes, [&](const auto &Saved) {
        const void *Object = Frame[Saved.first];
        return Object &&
               std::memcmp(Object, Saved.second.data(), Saved.second.size()) == 0;
      })) {
    *SlotOut = Slot;
    return It->second.Address;
  }
  void *Fn = nullptr;
  *SlotOut = nullptr;
  cppshRunStaged(static_cast<const CppshStagedStmt *>(Node), Frame, Slot, Entry,
                 nullptr, nullptr, &Fn, SlotOut);
  return Fn;
}

// What follows the call of a prepared run: how it left, given back; the
// result it kept named (a staged function's rest).
extern "C" int __cppsh_staged_done(const void *Node, int Left) {
  // Nothing in flight on this thread (a run that took the fast path): how it
  // left, as it is -- the in-flight runs this thread's own, no lock needed.
  if (CppshRunsInFlight.empty())
    return Left;
  std::lock_guard<std::recursive_mutex> Lock(CppshInterpreterLock);
  auto It = std::find_if(CppshRunsInFlight.rbegin(), CppshRunsInFlight.rend(),
                         [&](const CppshRunInFlight &R) { return R.Staged == Node; });
  if (It == CppshRunsInFlight.rend())
    return Left;
  CppshRunInFlight Run = std::move(*It);
  // Those after it threw (they never got here): dropped with it.
  CppshRunsInFlight.erase(std::prev(It.base()), CppshRunsInFlight.end());
  if (cppshTraceStaging() && CppshActiveInterpreter) {
    Sema &S = CppshActiveInterpreter->getCompilerInstance()->getSema();
    llvm::errs() << "cppsh-trace: ran staged "
                 << Run.Staged->getBeginLoc().printToString(S.getSourceManager())
                 << " entry " << Run.Entry << " left " << Left
                 << (Run.Keep ? (Run.ResultName.empty() ? " keeping nothing"
                                                        : " keeping " + Run.ResultName)
                              : std::string())
                 << "\n";
  }
  // Its return kept the result -- unless code staged inside it did (that
  // code's result kept already).
  if (Run.Keep && Left == 3 && !Run.ResultName.empty() &&
      CppshKeptResults == Run.KeptBefore) {
    CppshLastResult = Run.ResultName;
    CppshResultHistory.push_back(Run.ResultName);
    ++CppshKeptResults;
  }
  return Left;
}

extern "C" int __cppsh_staged_run(const void *Node, void *const *Frame,
                                  void *Slot, int Entry) {
  if (!CppshActiveInterpreter) {
    llvm::errs() << "error: cppsh: a staged statement cannot run: no interpreter\n";
    return 0;
  }
  std::lock_guard<std::recursive_mutex> Lock(CppshInterpreterLock);
  return cppshRunStaged(static_cast<const CppshStagedStmt *>(Node), Frame, Slot,
                        Entry);
}

// An expression parsed from the recorded tokens [Begin, End), compiled and
// run in a unit of its own: the value it gives kept in a global, __cppsh_vK,
// where Keep (a run-time template argument's), or discarded (a staged call,
// which leaves its own result).
static VarDecl *cppshRunTokens(Interpreter &Interp, unsigned Begin, unsigned End,
                               bool Keep, bool &Ok, bool IndexOf = false) {
  static unsigned Values = 0;
  Sema &S = Interp.getCompilerInstance()->getSema();
  ASTContext &Ctx = S.Context;
  const SourceLocation Loc;
  Ok = cppshReport(Interp.cppshBeginBuild());
  if (!Ok)
    return nullptr;
  VarDecl *Value = nullptr;
  ExprResult E;
  {
    // A top-level statement's own scope, as the parser makes one
    // (Parser::ParseTopLevelStmtDecl): its declaration context the scope's,
    // the translation unit's scope around it, where unqualified lookup ends
    // (made the statement's own context, lookup would walk past it).
    Parser &P = Interp.cppshParser();
    P.EnterScope(Scope::FnScope | Scope::DeclScope | Scope::CompoundStmtScope);
    TopLevelStmtDecl *Stmt = S.ActOnStartTopLevelStmtDecl(P.getCurScope());
    E = P.CppshParseTokens(Begin, End);
    // The index of the variant they make (a `*v`'s): E.index().
    if (IndexOf && E.isUsable()) {
      CXXScopeSpec SS;
      DeclarationNameInfo IndexName(
          &S.getPreprocessor().getIdentifierTable().get("index"), Loc);
      ExprResult Member = S.BuildMemberReferenceExpr(
          E.get(), E.get()->getType(), Loc, /*IsArrow=*/false, SS,
          SourceLocation(), /*FirstQualifierInScope=*/nullptr, IndexName,
          /*TemplateArgs=*/nullptr, /*S=*/nullptr);
      E = Member.isUsable()
              ? S.BuildCallExpr(nullptr, Member.get(), Loc, {}, Loc)
              : ExprError();
    }
    // A staged call in it is run here, as it is: no need of anything.
    CppshCutNeeded = false;
    CppshCutStagedCalls.clear();
    cppshEndNeedDiagnostics(S);
    ExprResult Full = E.isUsable() && !Keep
                          ? S.ActOnFinishFullExpr(E.get(), /*DiscardedValue=*/true)
                          : ExprError();
    S.ActOnFinishTopLevelStmtDecl(
        Stmt, Full.isUsable() ? static_cast<clang::Stmt *>(Full.get())
                              : new (Ctx) NullStmt(Loc));
    P.ExitScope();
    Interp.cppshAddBuilt(Stmt);
  }
  if (Keep && E.isUsable()) {
    const QualType T = E.get()->getType().getNonReferenceType().getUnqualifiedType();
    Value = VarDecl::Create(
        Ctx, Ctx.getTranslationUnitDecl(), Loc, Loc,
        &S.getPreprocessor().getIdentifierTable().get("__cppsh_v" +
                                                      std::to_string(Values++)),
        T, Ctx.getTrivialTypeSourceInfo(T, Loc), SC_None);
    S.AddInitializerToDecl(Value, E.get(), /*DirectInit=*/false);
    S.FinalizeDeclaration(Value);
    S.PushOnScopeChains(Value, S.TUScope);
    Interp.cppshAddBuilt(Value);
  }
  Ok = cppshReport(Interp.cppshEndBuildAndExecute()) && E.isUsable();
  return Ok ? Value : nullptr;
}

// A top-level declaration taken back for its staging, made ready to be parsed
// again from its tokens -- [Begin, End) of the recorded ones -- with what it
// needed supplied: a staged function's call it made (Hoist), run first, its
// result in its place; each run-time template argument of it, evaluated
// first, its value in its place.
// The results of the staged calls hoisted from the top-level declaration
// being staged (cppshStageDecl), in the order hoisted.
static std::vector<std::pair<SourceLocation, Expr *>> CppshHoistSupplies;

llvm::Error Interpreter::cppshStageDecl(unsigned Begin, unsigned End, bool Hoist) {
  Parser &P = cppshParser();
  Sema &S = getCompilerInstance()->getSema();
  ASTContext &Ctx = S.Context;
  if (cppshTraceStaging()) {
    auto Text = [&](SourceRange R) {
      return Lexer::getSourceText(CharSourceRange::getTokenRange(R),
                                  S.getSourceManager(), S.getLangOpts())
          .str();
    };
    llvm::errs() << "cppsh-trace: top-level declaration taken back ("
                 << (Hoist ? "a staged call" : "run-time template arguments")
                 << "), tokens " << Begin << ".." << End << "\n";
    if (Hoist)
      llvm::errs() << "cppsh-trace:   the call run first: '"
                   << Text({CppshHoistBegin, CppshHoistEnd}) << "'\n";
    else
      for (SourceRange Need : CppshTopNeedExprs)
        llvm::errs() << "cppsh-trace:   argument run first: '" << Text(Need)
                     << "'"
                     << (CppshVariantIndexNeeds.count(
                             Need.getBegin().getRawEncoding())
                             ? " (its .index())"
                             : "")
                     << "\n";
  }
  auto Fail = [](llvm::StringRef Why) {
    return llvm::make_error<llvm::StringError>(Why, std::error_code());
  };
  if (Hoist) {
    std::optional<unsigned> B = cppshTokenIndex(CppshHoistBegin);
    std::optional<unsigned> E = cppshTokenIndex(CppshHoistEnd);
    const SourceLocation At = CppshHoistBegin;
    if (!B || !E)
      return Fail("cppsh: the staged call's tokens are not known");
    CppshLastResult.clear();
    CppshInHoist = true;
    bool Ok = false;
    cppshRunTokens(*this, *B, *E + 1, /*Keep=*/false, Ok);
    CppshInHoist = false;
    if (!Ok)
      return Fail("cppsh: the staged call failed");
    LookupResult R(S, &S.getPreprocessor().getIdentifierTable().get(CppshLastResult),
                   SourceLocation(), Sema::LookupOrdinaryName);
    auto *Result = !CppshLastResult.empty() &&
                           S.LookupQualifiedName(R, Ctx.getTranslationUnitDecl())
                       ? R.getAsSingle<VarDecl>()
                       : nullptr;
    if (!Result)
      return Fail("cppsh: the staged call left no result");
    // Each staged call hoisted from this declaration so far supplied again:
    // the parser takes each supply once (a member call on the result begins
    // where the call does), and the declaration is parsed again whole.
    CppshHoistSupplies.push_back(
        {At, S.BuildDeclRefExpr(Result, Result->getType().getNonReferenceType(),
                                VK_LValue, At)});
    for (const auto &[Loc, Supplied] : CppshHoistSupplies)
      CppshSuppliedExprs[Loc.getRawEncoding()] = Supplied;
  } else {
    // Run in builds of their own: the declaration's need not theirs (their
    // FinishPTU would take them back for it), nor what they meet added to
    // the list walked.
    std::vector<SourceRange> Needs = std::exchange(CppshTopNeedExprs, {});
    CppshTopNeed = false;
    // One run for each argument, however many candidates of the call met
    // it (std::get's overloads each checked it).
    {
      llvm::SmallDenseSet<std::pair<SourceLocation::UIntTy, SourceLocation::UIntTy>, 8>
          Seen;
      llvm::erase_if(Needs, [&](SourceRange R) {
        return !Seen.insert({R.getBegin().getRawEncoding(),
                             R.getEnd().getRawEncoding()})
                    .second;
      });
    }
    for (SourceRange Need : Needs) {
      std::optional<unsigned> B = cppshTokenIndex(Need.getBegin());
      std::optional<unsigned> E = cppshTokenIndex(Need.getEnd());
      if (!B || !E)
        return Fail("cppsh: the run-time template argument's tokens are not known");
      bool Ok = false;
      // A `*v`'s index: the variant's tokens run, its index kept, supplied
      // where the `*` is.
      const auto IndexOf =
          CppshVariantIndexNeeds.find(Need.getBegin().getRawEncoding());
      const bool IsIndex = IndexOf != CppshVariantIndexNeeds.end();
      VarDecl *Value =
          cppshRunTokens(*this, *B, *E + 1, /*Keep=*/true, Ok, IsIndex);
      std::optional<APValue> Now = Value ? cppshRuntimeValueOf(Value) : std::nullopt;
      if (!Now)
        return Fail("cppsh: the run-time template argument's value is not known");
      const QualType T = Value->getType();
      const SourceLocation At = IsIndex ? IndexOf->second : Need.getBegin();
      // Its value, as a constant: a literal of an integer or a floating
      // type; otherwise the variable holding it, its value attached
      // (ConstantExpr) -- what a template argument of any type can be.
      Expr *Supplied = nullptr;
      if (Now->isInt()) {
        Supplied = IntegerLiteral::Create(Ctx, Now->getInt(), T, At);
      } else if (Now->isFloat()) {
        Supplied = FloatingLiteral::Create(Ctx, Now->getFloat(), /*isexact=*/true,
                                           T, At);
      } else {
        Expr *Ref = S.BuildDeclRefExpr(Value, T, VK_LValue, At);
        Expr *Read = ImplicitCastExpr::Create(Ctx, T, CK_LValueToRValue, Ref,
                                              nullptr, VK_PRValue,
                                              FPOptionsOverride());
        Supplied = ConstantExpr::Create(Ctx, Read, *Now);
      }
      CppshSuppliedExprs[At.getRawEncoding()] = Supplied;
    }
  }
  P.CppshRewind(Begin, End);
  return llvm::Error::success();
}

// Code run as the user typed it: its top-level declarations one at a time --
// each compiled and run before the next is parsed, so that each sees the
// values the ones before it made. One that needs the result of a staged
// function's call, or the value of a run-time template argument, of its own
// is taken back, what it needs run, and parsed again with it supplied.
// The code compiled for a staged statement kept for at most this many sets of
// values: older ones taken out (cppshTrimStaged), where nothing links to them.
static constexpr size_t CppshMaxInstances = 32;

// Between inputs -- no compiled code running, staged code's least of all --
// the statements compiled for more values than that lose their oldest.
static void cppshTrimStaged(Interpreter &Interp) {
  for (auto &[Staged, Instances] : CppshCompiled) {
    for (size_t I = 0; Instances.size() > CppshMaxInstances && I < Instances.size();) {
      CppshStagedCompiled &C = Instances[I];
      if (!Interp.cppshEvictStaged(C.Function)) {
        ++I;
        continue;
      }
      if (auto Last = CppshLastRuns.find(Staged);
          Last != CppshLastRuns.end() && Last->second.Address == C.Address)
        CppshLastRuns.erase(Last);
      Instances.erase(Instances.begin() + I);
    }
  }
}

// What was compiled of staged code in units taken back (a failed input's):
// forgotten -- the statements those units held, and the code compiled into
// them for any statement.
static void cppshForgetCompiledIn(ArrayRef<const TranslationUnitDecl *> Gone) {
  // (The code last run of each: none to be trusted now.)
  CppshLastRuns.clear();
  auto IsGone = [&](const Decl *D) {
    return D && llvm::is_contained(Gone, D->getTranslationUnitDecl());
  };
  for (auto It = CppshCompiled.begin(); It != CppshCompiled.end();) {
    if (IsGone(It->first->getStagedDecl())) {
      It = CppshCompiled.erase(It);
      continue;
    }
    llvm::erase_if(It->second, [&](const CppshStagedCompiled &C) {
      return IsGone(C.Function);
    });
    ++It;
  }
}

llvm::Error Interpreter::ParseAndExecute(llvm::StringRef Code, Value *V) {
  if (DeviceParser) {
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
  // An input of the user's (not one compiled code starts): staged code
  // compiled for many values trimmed first.
  static unsigned Depth = 0;
  ++Depth;
  auto Leave = llvm::scope_exit([&] { --Depth; });
  if (Depth == 1) {
    std::lock_guard<std::recursive_mutex> Lock(CppshInterpreterLock);
    cppshTrimStaged(*this);
  }
  if (llvm::Error Err = IncrParser->BeginInput(Code))
    return Err;
  Parser &P = cppshParser();
  unsigned Redos = 0;
  // The staged calls of the declaration being staged hoisted so far.
  llvm::SmallDenseSet<SourceLocation::UIntTy, 8> Hoisted;
  // A failed input taken back whole: each unit it made before the one that
  // failed -- run one top-level declaration at a time, they were compiled and
  // run -- out of the AST and the JIT, as Undo takes one back; what was
  // compiled of staged code in them forgotten. (What their code did as it ran
  // is done.)
  const size_t PTUsBefore = PTUs.size();
  auto Failed = [&](llvm::Error Err) -> llvm::Error {
    IncrParser->SkipInput();
    CppshHoistSupplies.clear();
    if (PTUs.size() > PTUsBefore) {
      std::vector<const TranslationUnitDecl *> Gone;
      for (auto It = std::next(PTUs.begin(), PTUsBefore); It != PTUs.end(); ++It)
        Gone.push_back(It->TUPart);
      if (llvm::Error UndoErr = Undo(PTUs.size() - PTUsBefore))
        Err = llvm::joinErrors(std::move(Err), std::move(UndoErr));
      cppshForgetCompiledIn(Gone);
    }
    return Err;
  };
  for (bool First = true;;) {
    // Off while it runs: what it compiles (the snapshots) names the same
    // variables, and would snapshot them again, without end.
    if (auto *Hook = CppshBeforeChunk) {
      CppshBeforeChunk = nullptr;
      Hook(*this, Code);
      CppshBeforeChunk = Hook;
    }
    CppshStageAt = SourceLocation();
    CppshHoistBegin = CppshHoistEnd = SourceLocation();
    CppshTopNeed = false;
    CppshTopNeedExprs.clear();
    auto Started = std::chrono::steady_clock::now();
    auto Since = [&] {
      auto Now = std::chrono::steady_clock::now();
      unsigned long long Ns =
          std::chrono::duration_cast<std::chrono::nanoseconds>(Now - Started).count();
      Started = Now;
      return Ns;
    };
    bool Done = false;
    // Parsed with the interpreter to itself (staged code on another thread
    // compiles meanwhile through the same Sema); run without it.
    llvm::Expected<TranslationUnitDecl *> TU = [&] {
      std::lock_guard<std::recursive_mutex> Lock(CppshInterpreterLock);
      return IncrParser->ParseNextTopLevel(First, Done);
    }();
    First = false;
    cppshEndNeedDiagnostics(getCompilerInstance()->getSema());
    CppshParseNs += Since();
    if (Done) {
      if (!TU)
        return TU.takeError();
      break;
    }
    const bool Hoist = CppshHoistBegin.isValid() && CppshHoistEnd.isValid();
    if (cppshTraceStaging())
      llvm::errs() << "cppsh-trace: top-level declaration parsed: "
                   << (TU ? "ok" : "taken back") << ", needs "
                   << (CppshTopNeed ? "run-time template arguments" : "none")
                   << (Hoist ? ", a staged call" : "") << "\n";
    // Parsed again as long as each time takes a step: a staged call not
    // hoisted yet (one per redo, however many the declaration makes), or
    // its run-time template arguments (all at once, a few times at most).
    const bool Progress =
        Hoist ? Hoisted.insert(CppshHoistBegin.getRawEncoding()).second
              : Redos++ < 4;
    if (!TU && (Hoist || CppshTopNeed) && Progress) {
      llvm::consumeError(TU.takeError());
      std::optional<unsigned> Begin =
          CppshTopLevelStarts.empty() ? std::nullopt
                                      : cppshTokenIndex(CppshTopLevelStarts.back());
      std::optional<unsigned> End =
          P.getCurToken().is(tok::eof)
              ? std::optional<unsigned>(CppshInputTokens.size())
              : cppshTokenIndex(P.getCurToken().getLocation());
      llvm::Error Err = Begin && End && *Begin < *End
                            ? cppshStageDecl(*Begin, *End, Hoist)
                            : llvm::make_error<llvm::StringError>(
                                  "cppsh: the declaration's tokens are not known",
                                  std::error_code());
      if (Err)
        return Failed(std::move(Err));
      continue;
    }
    Redos = 0;
    Hoisted.clear();
    CppshHoistSupplies.clear();
    CppshSuppliedExprs.clear();
    CppshVariantIndexNeeds.clear();
    if (!TU)
      return Failed(TU.takeError());
    PartialTranslationUnit &PTU = IncrParser->RegisterPTU(*TU);
    if (PTU.TheModule) {
      llvm::Error Err = Execute(PTU);
      CppshExecuteNs += Since();
      if (Err && cppshTraceStaging())
        llvm::errs() << "cppsh-trace: top-level declaration's code failed to run\n";
      if (Err)
        return Failed(std::move(Err));
    }
    if (LastValue.isValid()) {
      if (!V) {
        // What the input's own code wrote (stdio, buffered where the output
        // is a pipe or a file) first, then the value (llvm::outs).
        std::fflush(nullptr);
        LastValue.dump();
        llvm::outs().flush();
        LastValue.clear();
      } else
        *V = std::move(LastValue);
    }
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

    // Its module is out of the JIT already; code generation forgets its decls
    // (deferred ones, mangled names), so what is parsed again in their place
    // is not a second definition of the same name.
    if (CodeGenerator *CG = Act->getCodeGen())
      CG->DiscardIncrementalUnit(PTUs.back().TUPart, /*ThrowModuleAway=*/false);
    IncrParser->CleanUpPTU(PTUs.back().TUPart);
    PTUs.pop_back();
  }
  return llvm::Error::success();
}

llvm::Expected<std::pair<std::string, std::vector<std::string>>>
Interpreter::compileKeepingObject(llvm::StringRef Code) {
  auto PTU = Parse(Code);
  if (!PTU)
    return PTU.takeError();
  std::string Object;
  std::vector<std::string> Defines;
  if (PTU->TheModule) {
    llvm::Error EmitErr = llvm::Error::success();
    TSCtx->withContextDo([&](llvm::LLVMContext *) {
      std::unique_ptr<llvm::Module> Copy = llvm::CloneModule(*PTU->TheModule);
      for (llvm::GlobalValue &GV : Copy->global_values())
        if (!GV.isDeclaration() && GV.hasExternalLinkage() && GV.hasName())
          Defines.push_back(GV.getName().str());
      // As the JIT compiles: the host, the -O0 backend; position-independent,
      // for JITLink to place it anywhere.
      auto JTMB = llvm::orc::JITTargetMachineBuilder::detectHost();
      if (!JTMB) {
        EmitErr = JTMB.takeError();
        return;
      }
      JTMB->setCodeGenOptLevel(llvm::CodeGenOptLevel::None);
      JTMB->setRelocationModel(llvm::Reloc::PIC_);
      auto TM = JTMB->createTargetMachine();
      if (!TM) {
        EmitErr = TM.takeError();
        return;
      }
      Copy->setDataLayout((*TM)->createDataLayout());
      llvm::SmallVector<char, 0> Buffer;
      llvm::raw_svector_ostream OS(Buffer);
      llvm::legacy::PassManager PM;
      if ((*TM)->addPassesToEmitFile(PM, OS, nullptr, llvm::CodeGenFileType::ObjectFile)) {
        EmitErr = llvm::make_error<llvm::StringError>("cannot emit an object file",
                                                      llvm::inconvertibleErrorCode());
        return;
      }
      PM.run(*Copy);
      Object.assign(Buffer.begin(), Buffer.end());
    });
    if (EmitErr)
      return std::move(EmitErr);
    if (llvm::Error Err = Execute(*PTU))
      return std::move(Err);
  }
  return std::make_pair(std::move(Object), std::move(Defines));
}

llvm::Error Interpreter::cppshBeginBuild() { return IncrParser->BeginBuild(); }

void Interpreter::cppshAddBuilt(Decl *D) { IncrParser->AddBuilt(DeclGroupRef(D)); }

Parser &Interpreter::cppshParser() { return IncrParser->getParser(); }

bool Interpreter::cppshEvictStaged(FunctionDecl *F) {
  CodeGenerator *CG = Act->getCodeGen();
  if (!F || !CG)
    return false;
  TranslationUnitDecl *TU = F->getTranslationUnitDecl();
  auto It = llvm::find_if(PTUs, [&](const PartialTranslationUnit &P) {
    return P.TUPart == TU;
  });
  if (It == PTUs.end() ||
      CG->ExportsIncrementally(TU, CG->GetMangledName(GlobalDecl(F))))
    return false;
  if (IncrExecutor)
    if (llvm::Error Err = IncrExecutor->removeModule(*It)) {
      llvm::consumeError(std::move(Err));
      return false;
    }
  CG->DiscardIncrementalUnit(TU, /*ThrowModuleAway=*/false);
  IncrParser->CleanUpPTU(TU);
  cppshForgetSpecializationsIn(TU);
  PTUs.erase(It);
  return true;
}

llvm::Error Interpreter::cppshEndBuildAndExecute() {
  llvm::Expected<TranslationUnitDecl *> TU = IncrParser->EndBuild();
  if (!TU)
    return TU.takeError();
  PartialTranslationUnit &PTU = IncrParser->RegisterPTU(*TU);
  return PTU.TheModule ? Execute(PTU) : llvm::Error::success();
}

llvm::Error Interpreter::loadCompiledObject(llvm::StringRef Object,
                                            llvm::ArrayRef<std::string> Defines) {
  auto EE = getExecutionEngine();
  if (!EE)
    return EE.takeError();
  if (llvm::Error Err =
          EE->addObjectFile(llvm::MemoryBuffer::getMemBufferCopy(Object, "cppsh-warm.o")))
    return Err;
  if (CodeGenerator *CG = Act->getCodeGen())
    for (const std::string &Name : Defines)
      CG->MarkIncrementalExported(Name);
  return llvm::Error::success();
}

llvm::Error Interpreter::LoadDynamicLibrary(const char *name) {
  auto EEOrErr = getExecutionEngine();
  if (!EEOrErr)
    return EEOrErr.takeError();

  return EEOrErr->LoadDynamicLibrary(name);
}
} // end namespace clang
