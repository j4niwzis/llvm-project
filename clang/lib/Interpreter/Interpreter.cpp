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
#include "clang/AST/QualTypeNames.h"
#include "clang/Sema/CppshStaging.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Sema.h"
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
extern llvm::DenseMap<const ParmVarDecl *, APValue> CppshParamValue;
extern llvm::DenseMap<const ParmVarDecl *, const Expr *> CppshParamRebuild;
bool cppshMutates(const Stmt *S, const VarDecl *VD);
extern bool CppshTopNeed;
extern bool CppshCutNeeded;
extern std::vector<SourceRange> CppshTopNeedExprs;
extern SourceLocation CppshHoistBegin, CppshHoistEnd;
extern bool CppshInHoist;

// The global holding the last continuation's result: what a hoisted call is
// replaced by.
static std::string CppshLastResult;
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

// The global naming a live local in a frame, built: `T &Name = *(T *)Addr;`.
static VarDecl *cppshFrameGlobal(Sema &S, IdentifierInfo *Name, QualType T,
                                 void *Addr) {
  ASTContext &Ctx = S.Context;
  const SourceLocation Loc;
  const QualType RefT = Ctx.getLValueReferenceType(T);
  auto *VD = VarDecl::Create(Ctx, Ctx.getTranslationUnitDecl(), Loc, Loc, Name,
                             RefT, Ctx.getTrivialTypeSourceInfo(RefT, Loc),
                             SC_None);
  Expr *Int = IntegerLiteral::Create(
      Ctx, llvm::APInt(64, llvm::bit_cast<uintptr_t>(Addr)),
      Ctx.UnsignedLongLongTy, Loc);
  ExprResult Ptr = S.BuildCStyleCastExpr(
      Loc, Ctx.getTrivialTypeSourceInfo(Ctx.getPointerType(T), Loc), Loc, Int);
  ExprResult Obj = Ptr.isUsable()
                       ? S.CreateBuiltinUnaryOp(Loc, UO_Deref, Ptr.get())
                       : ExprError();
  if (!Obj.isUsable())
    return nullptr;
  S.AddInitializerToDecl(VD, Obj.get(), /*DirectInit=*/false);
  S.FinalizeDeclaration(VD);
  S.PushOnScopeChains(VD, S.TUScope);
  return VD;
}

using CppshGlobals = SmallVector<std::pair<const CppshCutLocal *, VarDecl *>, 8>;

static bool cppshReport(llvm::Error Err) {
  if (!Err)
    return true;
  llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
  return false;
}

// A frame (a cut's, a step's) laid out for what is compiled with it: the
// run-time template arguments' values, for its compile to take in order;
// each live local a global naming it -- built and run first, so that the
// value specialization reads their values, and what is not plain data
// snapshotted (rebuilt from that).
static bool cppshFrameGlobals(Interpreter &Interp, Sema &S,
                              const std::string &Tag,
                              ArrayRef<CppshCutLocal> Locals,
                              void *const *Frame, std::vector<APValue> &Needs,
                              CppshGlobals &Globals) {
  IdentifierTable &Idents = S.getPreprocessor().getIdentifierTable();
  const bool AnyLocal = llvm::any_of(
      Locals, [](const CppshCutLocal &L) { return L.Name != nullptr; });
  const bool Building = AnyLocal && cppshReport(Interp.cppshBeginBuild());
  bool Ok = !AnyLocal || Building;
  for (unsigned I = 0; I < Locals.size(); ++I) {
    const CppshCutLocal &L = Locals[I];
    if (!L.Name) {
      const long long V = *static_cast<const long long *>(Frame[I]);
      Needs.push_back(APValue(llvm::APSInt(
          llvm::APInt(64, static_cast<uint64_t>(V), /*isSigned=*/true),
          /*isUnsigned=*/false)));
      continue;
    }
    if (!Building)
      continue;
    VarDecl *G = cppshFrameGlobal(
        S, &Idents.get("__cppsh_f" + Tag + "_" + L.Name->getName().str()),
        L.Type, Frame[I]);
    if (!G) {
      Ok = false;
      continue;
    }
    Interp.cppshAddBuilt(G);
    Globals.emplace_back(&L, G);
  }
  if (!Building)
    return Ok;
  if (!cppshReport(Interp.cppshEndBuildAndExecute()))
    return false;
  // The snapshots, in a unit of their own: a type that cannot be
  // snapshotted only loses its rebuilt value.
  SmallVector<VarDecl *, 4> ToSnap;
  for (const auto &Global : Globals)
    if (!Global.first->Type->isDependentType() &&
        !Global.first->Type.isTriviallyCopyableType(S.Context))
      ToSnap.push_back(Global.second);
  llvm::consumeError(Interp.cppshSnapshot(ToSnap));
  return Ok;
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
      TopLevelStmtDecl *Stmt = S.ActOnStartTopLevelStmtDecl(S.TUScope);
      Expr *Ref = S.BuildDeclRefExpr(G, G->getType().getNonReferenceType(),
                                     VK_LValue, Loc);
      ExprResult Call = S.BuildCallExpr(S.TUScope, Snap.get(), Loc, Ref, Loc);
      ExprResult Full = Call.isUsable()
                            ? S.ActOnFinishFullExpr(Call.get(), /*DiscardedValue=*/true)
                            : ExprError();
      S.ActOnFinishTopLevelStmtDecl(
          Stmt, Full.isUsable() ? static_cast<clang::Stmt *>(Full.get())
                                : new (Ctx) NullStmt(Loc));
      Interp.cppshAddBuilt(Stmt);
    }
  }
  return cppshEndBuildAndExecute();
}

namespace {
// What staging changes while compiling for a frame, put back after.
struct CppshFrameState {
  bool WasHoist = std::exchange(CppshInHoist, false);
  ~CppshFrameState() { CppshInHoist = WasHoist; }
};
} // namespace

// std::sh::__cppsh_region_tag, the variable template whose specializations
// name a region's closure type and its arguments' types (each one's address
// what __cppsh_region hands over).
static VarTemplateDecl *cppshRegionTagTemplate(Sema &S) {
  NamespaceDecl *Std = S.getStdNamespace();
  if (!Std)
    return nullptr;
  IdentifierTable &Idents = S.getPreprocessor().getIdentifierTable();
  LookupResult ShR(S, &Idents.get("sh"), SourceLocation(),
                   Sema::LookupNamespaceName);
  S.LookupQualifiedName(ShR, Std);
  auto *Sh = ShR.getAsSingle<NamespaceDecl>();
  if (!Sh)
    return nullptr;
  LookupResult R(S, &Idents.get("__cppsh_region_tag"), SourceLocation(),
                 Sema::LookupOrdinaryName);
  S.LookupQualifiedName(R, Sh);
  return R.getAsSingle<VarTemplateDecl>();
}

// A staged region run (Parser::CppshEmitRegion), as the function it is in
// runs: its call operator instantiated with the values of the locals and
// arguments it is handed -- read from the frame (or rebuilt from their
// snapshots), each a value it is compiled with unless it changes it -- and
// called with them, in their frame. One instantiation for each set of values
// (its __cppsh_key), found again for the same values.
static void cppshRunRegion(const void *Tag, void *Closure, void *const *Frame,
                           unsigned N, bool Keep) {
  if (!CppshActiveInterpreter)
    return;
  Interpreter &Interp = *CppshActiveInterpreter;
  Sema &S = Interp.getCompilerInstance()->getSema();
  ASTContext &Ctx = S.Context;
  const SourceLocation Loc;

  // Which region: the specialization of __cppsh_region_tag at Tag.
  static llvm::DenseMap<const void *, VarTemplateSpecializationDecl *> Tags;
  VarTemplateSpecializationDecl *Spec = Tags.lookup(Tag);
  if (!Spec)
    if (VarTemplateDecl *VTD = cppshRegionTagTemplate(S))
      for (VarTemplateSpecializationDecl *Candidate : VTD->specializations()) {
        llvm::Expected<llvm::orc::ExecutorAddr> Addr =
            Interp.getSymbolAddress(GlobalDecl(Candidate));
        if (!Addr) {
          llvm::consumeError(Addr.takeError());
          continue;
        }
        if (Addr->toPtr<const void *>() == Tag) {
          Tags[Tag] = Spec = Candidate;
          break;
        }
      }
  if (!Spec || Spec->getTemplateArgs().size() != 2)
    return;
  const QualType ClosureType = Spec->getTemplateArgs()[0].getAsType();
  ArrayRef<TemplateArgument> ArgTypes =
      Spec->getTemplateArgs()[1].getPackAsArray();
  auto *RD = ClosureType->getAsCXXRecordDecl();
  FunctionTemplateDecl *CallTemplate =
      RD ? RD->getDependentLambdaCallOperator() : nullptr;
  FunctionDecl *Pattern = CallTemplate ? CallTemplate->getTemplatedDecl() : nullptr;
  if (!Pattern || Pattern->getNumParams() != N || ArgTypes.size() != N)
    return;

  const std::string Unit = std::to_string(CppshContinuations++);
  CppshFrameState State;
  // Its frame: the arguments, then the closure itself.
  std::vector<CppshCutLocal> Locals;
  SmallVector<void *, 8> Addresses(Frame, Frame + N);
  IdentifierTable &Idents = S.getPreprocessor().getIdentifierTable();
  for (unsigned I = 0; I < N; ++I)
    Locals.push_back({&Idents.get("a" + std::to_string(I)),
                      ArgTypes[I].getAsType().getNonReferenceType(), false,
                      /*ByRef=*/true});
  Locals.push_back({&Idents.get("closure"), ClosureType, false, /*ByRef=*/true});
  Addresses.push_back(Closure);
  std::vector<APValue> Needs;
  CppshGlobals Globals;
  if (!cppshFrameGlobals(Interp, S, Unit, Locals, Addresses.data(), Needs, Globals) ||
      Globals.size() != N + 1)
    return;
  // A staged function's call it was handed (a std::sh::staged): the result
  // that call left, its value, in its place.
  for (unsigned I = 0; I < N; ++I) {
    auto *Arg = Locals[I].Type->getAsCXXRecordDecl();
    if (!Arg || !Arg->getIdentifier() || Arg->getName() != "staged")
      continue;
    LookupResult R(S, &Idents.get(CppshLastResult), Loc, Sema::LookupOrdinaryName);
    auto *Result = !CppshLastResult.empty() &&
                           S.LookupQualifiedName(R, Ctx.getTranslationUnitDecl())
                       ? R.getAsSingle<VarDecl>()
                       : nullptr;
    if (!Result)
      return;
    Locals[I].Type = Result->getType().getNonReferenceType();
    Globals[I].second = Result;
  }

  // The values it is compiled with: each parameter it does not change.
  Stmt *Body = Pattern->getBody();
  llvm::FoldingSetNodeID Values;
  SmallVector<std::pair<ParmVarDecl *, std::optional<APValue>>, 8> SavedValues;
  SmallVector<std::pair<ParmVarDecl *, const Expr *>, 8> SavedRebuilds;
  for (unsigned I = 0; I < N; ++I) {
    ParmVarDecl *P = Pattern->getParamDecl(I);
    VarDecl *G = Globals[I].second;
    if (!Body || cppshMutates(Body, P)) {
      Values.AddInteger(0u);
      continue;
    }
    if (std::optional<APValue> V = cppshRuntimeValueOf(G)) {
      Values.AddInteger(1u);
      V->Profile(Values);
      auto Known = CppshParamValue.find(P);
      SavedValues.push_back({P, Known == CppshParamValue.end()
                                    ? std::nullopt
                                    : std::optional<APValue>(Known->second)});
      CppshParamValue[P] = std::move(*V);
    } else if (Expr *Rebuild = cppshRuntimeRebuildOf(S, G)) {
      Values.AddInteger(2u);
      Rebuild->Profile(Values, Ctx, /*Canonical=*/true);
      SavedRebuilds.push_back({P, CppshParamRebuild.lookup(P)});
      CppshParamRebuild[P] = Rebuild;
    } else {
      Values.AddInteger(0u);
    }
  }
  // Its key: one for each set of values, in the order first met.
  static std::map<const FunctionTemplateDecl *, std::vector<llvm::FoldingSetNodeID>>
      Keys;
  std::vector<llvm::FoldingSetNodeID> &Known = Keys[CallTemplate];
  unsigned Key = llvm::find(Known, Values) - Known.begin();
  if (Key == Known.size())
    Known.push_back(Values);

  // closure.operator()<Key>(a0, a1, ...), a top-level statement.
  const bool WasNeeded = std::exchange(CppshCutNeeded, false);
  if (cppshReport(Interp.cppshBeginBuild())) {
    TopLevelStmtDecl *Stmt = S.ActOnStartTopLevelStmtDecl(S.TUScope);
    Expr *Base = S.BuildDeclRefExpr(Globals[N].second, ClosureType, VK_LValue, Loc);
    Expr *KeyLit = IntegerLiteral::Create(
        Ctx, llvm::APInt(Ctx.getIntWidth(Ctx.UnsignedIntTy), Key),
        Ctx.UnsignedIntTy, Loc);
    TemplateArgumentListInfo TemplateArgs(Loc, Loc);
    TemplateArgs.addArgument(
        TemplateArgumentLoc(TemplateArgument(KeyLit, /*IsCanonical=*/false), KeyLit));
    CXXScopeSpec SS;
    DeclarationNameInfo Name(Ctx.DeclarationNames.getCXXOperatorName(OO_Call), Loc);
    ExprResult Member = S.BuildMemberReferenceExpr(
        Base, ClosureType, Loc, /*IsArrow=*/false, SS, SourceLocation(), nullptr,
        Name, &TemplateArgs, S.TUScope);
    SmallVector<Expr *, 8> Args;
    for (unsigned I = 0; I < N; ++I)
      Args.push_back(S.BuildDeclRefExpr(Globals[I].second,
                                        Globals[I].first->Type, VK_LValue, Loc));
    ExprResult Call = Member.isUsable()
                          ? S.BuildCallExpr(S.TUScope, Member.get(), Loc, Args, Loc)
                          : ExprError();
    // A need met as it was instantiated: a value it changes (no constant).
    cppshEndNeedDiagnostics(S);
    if (CppshCutNeeded) {
      S.Diag(Pattern->getLocation(),
             S.getDiagnostics().getCustomDiagID(
                 DiagnosticsEngine::Error,
                 "this needs the value of a variable it changes itself: not staged"));
      Call = ExprError();
    }
    // Its result kept (a staged function's: __cppsh_region_staged), where it
    // gives one: a global, __cppsh_resK, for whoever waits for it.
    const bool Result = Keep && Call.isUsable() &&
                        !Call.get()->getType()->isVoidType();
    ExprResult Full = Call.isUsable() && !Result
                          ? S.ActOnFinishFullExpr(Call.get(), /*DiscardedValue=*/true)
                          : ExprError();
    S.ActOnFinishTopLevelStmtDecl(
        Stmt, Full.isUsable() ? static_cast<clang::Stmt *>(Full.get())
                              : new (Ctx) NullStmt(Loc));
    Interp.cppshAddBuilt(Stmt);
    bool Value = false;
    std::string ResultName = "__cppsh_res" + Unit;
    if (Result) {
      const QualType T =
          Call.get()->getType().getNonReferenceType().getUnqualifiedType();
      auto *Res = VarDecl::Create(Ctx, Ctx.getTranslationUnitDecl(), Loc, Loc,
                                  &Idents.get(ResultName), T,
                                  Ctx.getTrivialTypeSourceInfo(T, Loc), SC_None);
      S.AddInitializerToDecl(Res, Call.get(), /*DirectInit=*/false);
      S.FinalizeDeclaration(Res);
      S.PushOnScopeChains(Res, S.TUScope);
      Interp.cppshAddBuilt(Res);
      auto *RecordType = T->getAsCXXRecordDecl();
      Value = !(RecordType && RecordType->getIdentifier() &&
                RecordType->getName() == "staged");
    }
    if (cppshReport(Interp.cppshEndBuildAndExecute()) && Value)
      CppshLastResult = ResultName;
  }
  CppshCutNeeded = WasNeeded;
  for (auto &[P, Was] : llvm::reverse(SavedRebuilds)) {
    if (Was)
      CppshParamRebuild[P] = Was;
    else
      CppshParamRebuild.erase(P);
  }
  for (auto &[P, Was] : llvm::reverse(SavedValues)) {
    if (Was)
      CppshParamValue[P] = std::move(*Was);
    else
      CppshParamValue.erase(P);
  }
}

extern "C" void __cppsh_region_run(const void *Tag, void *Closure,
                                   void *const *Frame, unsigned N) {
  cppshRunRegion(Tag, Closure, Frame, N, /*Keep=*/false);
}

// The rest of a staged function's body made a region: its result kept.
extern "C" void __cppsh_region_run_staged(const void *Tag, void *Closure,
                                          void *const *Frame, unsigned N) {
  cppshRunRegion(Tag, Closure, Frame, N, /*Keep=*/true);
}

// An expression parsed from the recorded tokens [Begin, End), compiled and
// run in a unit of its own: the value it gives kept in a global, __cppsh_vK,
// where Keep (a run-time template argument's), or discarded (a staged call,
// which leaves its own result).
static VarDecl *cppshRunTokens(Interpreter &Interp, unsigned Begin, unsigned End,
                               bool Keep, bool &Ok) {
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
    TopLevelStmtDecl *Stmt = S.ActOnStartTopLevelStmtDecl(S.TUScope);
    E = Interp.cppshParser().CppshParseTokens(Begin, End);
    ExprResult Full = E.isUsable() && !Keep
                          ? S.ActOnFinishFullExpr(E.get(), /*DiscardedValue=*/true)
                          : ExprError();
    S.ActOnFinishTopLevelStmtDecl(
        Stmt, Full.isUsable() ? static_cast<clang::Stmt *>(Full.get())
                              : new (Ctx) NullStmt(Loc));
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
llvm::Error Interpreter::cppshStageDecl(unsigned Begin, unsigned End, bool Hoist) {
  Parser &P = cppshParser();
  Sema &S = getCompilerInstance()->getSema();
  ASTContext &Ctx = S.Context;
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
    P.CppshSuppliedExprs[At.getRawEncoding()] = S.BuildDeclRefExpr(
        Result, Result->getType().getNonReferenceType(), VK_LValue, At);
  } else {
    for (SourceRange Need : CppshTopNeedExprs) {
      std::optional<unsigned> B = cppshTokenIndex(Need.getBegin());
      std::optional<unsigned> E = cppshTokenIndex(Need.getEnd());
      if (!B || !E)
        return Fail("cppsh: the run-time template argument's tokens are not known");
      bool Ok = false;
      VarDecl *Value = cppshRunTokens(*this, *B, *E + 1, /*Keep=*/true, Ok);
      std::optional<APValue> Now = Value ? cppshRuntimeValueOf(Value) : std::nullopt;
      if (!Now || !Now->isInt())
        return Fail("cppsh: the run-time template argument gave no integer");
      const QualType T = Value->getType();
      P.CppshSuppliedExprs[Need.getBegin().getRawEncoding()] =
          IntegerLiteral::Create(Ctx, Now->getInt(), T, Need.getBegin());
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
  if (llvm::Error Err = IncrParser->BeginInput(Code))
    return Err;
  Parser &P = cppshParser();
  unsigned Redos = 0;
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
    llvm::Expected<TranslationUnitDecl *> TU =
        IncrParser->ParseNextTopLevel(First, Done);
    First = false;
    cppshEndNeedDiagnostics(getCompilerInstance()->getSema());
    CppshParseNs += Since();
    if (Done) {
      if (!TU)
        return TU.takeError();
      break;
    }
    const bool Hoist = CppshHoistBegin.isValid() && CppshHoistEnd.isValid();
    if (!TU && (Hoist || CppshTopNeed) && Redos++ < 4) {
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
      if (Err) {
        IncrParser->SkipInput();
        return Err;
      }
      continue;
    }
    Redos = 0;
    P.CppshSuppliedExprs.clear();
    if (!TU) {
      IncrParser->SkipInput();
      return TU.takeError();
    }
    PartialTranslationUnit &PTU = IncrParser->RegisterPTU(*TU);
    if (PTU.TheModule) {
      llvm::Error Err = Execute(PTU);
      CppshExecuteNs += Since();
      if (Err) {
        IncrParser->SkipInput();
        return Err;
      }
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
