//===--- SemaCppsh.cpp - Semantic analysis for cppsh staged statements ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements semantic analysis for cppsh's staged statements: code
//  of a function that needs a value only running the function gives, parsed
//  in a dependent context of its own (CppshStagedDecl) and instantiated, as
//  the function runs, for the values it has then.
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtCXX.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/CppshStaging.h"
#include "clang/Sema/Initialization.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/ScopeInfo.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/Template.h"
#include "llvm/ADT/ScopeExit.h"
#include <set>

using namespace clang;

namespace clang {
extern std::set<const FunctionDecl *> CppshCutFunctions;
} // namespace clang

namespace {
// Whether code uses `this` (written, or implied by a member's name).
struct CppshFindThis : RecursiveASTVisitor<CppshFindThis> {
  bool Found = false;
  bool VisitCXXThisExpr(CXXThisExpr *) {
    Found = true;
    return false;
  }
};

// The labels code defines, and those its gotos jump to.
struct CppshJumps : RecursiveASTVisitor<CppshJumps> {
  llvm::SmallPtrSet<const LabelDecl *, 4> Defined;
  SmallVector<LabelDecl *, 4> Gone;
  bool VisitLabelStmt(LabelStmt *S) {
    Defined.insert(S->getDecl());
    return true;
  }
  bool VisitGotoStmt(GotoStmt *S) {
    Gone.push_back(S->getLabel());
    return true;
  }
};

// Where code may be entered from outside it: its labels, and the case and
// default labels of a switch around it (not of one in it).
struct CppshEntries : RecursiveASTVisitor<CppshEntries> {
  SmallVector<Stmt *, 4> Entries;
  unsigned SwitchDepth = 0;
  bool TraverseSwitchStmt(SwitchStmt *S) {
    ++SwitchDepth;
    bool Result = RecursiveASTVisitor::TraverseSwitchStmt(S);
    --SwitchDepth;
    return Result;
  }
  // A lambda's body is its own.
  bool TraverseLambdaExpr(LambdaExpr *) { return true; }
  bool VisitCaseStmt(CaseStmt *S) {
    if (!SwitchDepth)
      Entries.push_back(S);
    return true;
  }
  bool VisitDefaultStmt(DefaultStmt *S) {
    if (!SwitchDepth)
      Entries.push_back(S);
    return true;
  }
  bool VisitLabelStmt(LabelStmt *S) {
    Entries.push_back(S);
    return true;
  }
};

static SmallVector<Stmt *, 4> cppshEntriesOf(Stmt *Body) {
  CppshEntries E;
  E.TraverseStmt(Body);
  return std::move(E.Entries);
}

// The location an entry is known by.
static SourceLocation cppshEntryLoc(const Stmt *E) {
  if (const auto *SC = dyn_cast<SwitchCase>(E))
    return SC->getKeywordLoc();
  if (const auto *L = dyn_cast<LabelStmt>(E))
    return L->getIdentLoc();
  return SourceLocation();
}

// The declarations code names.
struct CppshUses : RecursiveASTVisitor<CppshUses> {
  llvm::SmallPtrSet<const Decl *, 16> Used;
  bool VisitDeclRefExpr(DeclRefExpr *E) {
    Used.insert(E->getDecl());
    return true;
  }
};
} // namespace

CppshStagedDecl *Sema::ActOnStartCppshStaged(Scope *BodyScope,
                                             SourceLocation Loc,
                                             ArrayRef<VarDecl *> Locals,
                                             Expr *StagedCall,
                                             unsigned TemplateDepth,
                                             bool KeepsResult) {
  auto *SD = CppshStagedDecl::Create(Context, CurContext, Loc);
  CurContext->addDecl(SD);
  if (sema::FunctionScopeInfo *FSI = getCurFunction())
    FSI->HasCppshStaged = true;
  // The type of the staged function's result it uses: a type parameter of
  // it, given as the statement runs.
  TemplateTypeParmDecl *ResultT = nullptr;
  if (StagedCall) {
    ResultT = TemplateTypeParmDecl::Create(
        Context, Context.getTranslationUnitDecl(), Loc, Loc, TemplateDepth,
        /*P=*/0, /*Id=*/nullptr, /*Typename=*/true, /*ParameterPack=*/false);
    SD->setResultTypeParm(ResultT);
  }
  CppshStagedScope Info;
  Info.Decl = SD;
  Info.BodyScope = BodyScope;
  Info.KeepsResult = KeepsResult;
  Info.Locals.assign(Locals.begin(), Locals.end());
  Info.StagedCall = StagedCall;
  Info.Outer = CurContext;
  PushDeclContext(BodyScope, SD);
  // A staged parameter for each local it names, found in its place.
  SmallVector<ImplicitParamDecl *, 8> Params;
  for (VarDecl *VD : Locals) {
    auto *P = ImplicitParamDecl::Create(Context, SD, VD->getLocation(),
                                        VD->getIdentifier(), VD->getType(),
                                        ImplicitParamKind::CppshStaged);
    PushOnScopeChains(P, BodyScope);
    Params.push_back(P);
  }
  if (ResultT) {
    QualType T = Context.getTemplateTypeParmType(TemplateDepth, 0,
                                                 /*ParameterPack=*/false,
                                                 ResultT);
    auto *P = ImplicitParamDecl::Create(
        Context, SD, Loc, &PP.getIdentifierTable().get("__cppsh_result"), T,
        ImplicitParamKind::CppshStaged);
    SD->addDecl(P);
    Params.push_back(P);
  }
  SD->setParameters(Context, Params);
  CppshStagedScopes.push_back(std::move(Info));
  return SD;
}

void Sema::ActOnCppshStagedSupply(CppshStagedDecl *SD, SourceLocation Loc,
                                  VarDecl *Local) {
  if (CppshStagedScopes.empty() || CppshStagedScopes.back().Decl != SD)
    return;
  CppshStagedScope &Info = CppshStagedScopes.back();
  const auto *It = llvm::find(Info.Locals, Local);
  if (It == Info.Locals.end())
    return;
  SmallVector<std::pair<SourceLocation, unsigned>, 2> All(SD->supplies());
  All.push_back({Loc, static_cast<unsigned>(It - Info.Locals.begin())});
  SD->setSupplies(Context, All);
}

StmtResult Sema::ActOnFinishCppshStaged(CppshStagedDecl *SD, Stmt *Body,
                                        SourceLocation EndLoc) {
  if (CppshStagedScopes.empty() || CppshStagedScopes.back().Decl != SD)
    return StmtError();
  CppshStagedScope Info = CppshStagedScopes.pop_back_val();
  PopDeclContext();
  if (!Body)
    return StmtError();
  // The locals its body names: the others no part of it (nor of the values
  // it is compiled for).
  CppshUses Uses;
  Uses.TraverseStmt(Body);
  ArrayRef<ImplicitParamDecl *> All = SD->parameters();
  SmallVector<ImplicitParamDecl *, 8> Kept;
  SmallVector<VarDecl *, 8> KeptLocals;
  SmallVector<unsigned, 8> NewIndex(All.size(), ~0u);
  for (unsigned I = 0; I < All.size(); ++I) {
    const bool IsLocal = I < Info.Locals.size();
    // A supplied argument's value is used where the default is, unseen.
    const bool Supplied = llvm::any_of(
        SD->supplies(), [&](const auto &S) { return S.second == I; });
    if (IsLocal && !Supplied && !Uses.Used.count(All[I])) {
      SD->removeDecl(All[I]);
      continue;
    }
    NewIndex[I] = Kept.size();
    Kept.push_back(All[I]);
    if (IsLocal)
      KeptLocals.push_back(Info.Locals[I]);
  }
  SD->setParameters(Context, Kept);
  SmallVector<std::pair<SourceLocation, unsigned>, 2> Supplies;
  for (const auto &[Loc, Index] : SD->supplies())
    if (Index < NewIndex.size() && NewIndex[Index] != ~0u)
      Supplies.push_back({Loc, NewIndex[Index]});
  SD->setSupplies(Context, Supplies);
  Info.Locals = std::move(KeptLocals);
  // Its frame: each local, as the function around it names it; the staged
  // call; `this`, where it uses it.
  const SourceLocation Loc = SD->getLocation();
  SmallVector<Expr *, 8> Frame;
  for (VarDecl *VD : Info.Locals)
    Frame.push_back(BuildDeclRefExpr(VD, VD->getType().getNonReferenceType(),
                                     VK_LValue, Loc));
  if (Info.StagedCall)
    Frame.push_back(Info.StagedCall);
  CppshFindThis Finder;
  Finder.TraverseStmt(Body);
  if (Finder.Found) {
    QualType ThisTy = getCurrentThisType();
    if (ThisTy.isNull())
      return StmtError();
    Frame.push_back(BuildCXXThisExpr(Loc, ThisTy, /*IsImplicit=*/true));
    SD->setUsesThis(true);
  }
  // The labels outside it its gotos jump to.
  CppshJumps Jumps;
  Jumps.TraverseStmt(Body);
  SmallVector<LabelDecl *, 4> Targets;
  for (LabelDecl *L : Jumps.Gone)
    if (L && !Jumps.Defined.count(L) && !llvm::is_contained(Targets, L))
      Targets.push_back(L);
  if (!Targets.empty())
    Info.Leaves |= CppshStagedStmt::LeavesByGoto;
  auto *S = CppshStagedStmt::Create(Context, SD, Body, Frame, Info.Leaves,
                                    Info.KeepsResult, Loc, EndLoc);
  S->setGotoTargets(Context, Targets, SmallVector<int, 4>(Targets.size(), -1));
  S->setEntries(Context, cppshEntriesOf(Body));
  SD->setStagedStmt(S);
  if (Info.Suspends) {
    SD->setSuspends(true);
    if (!BuildCppshStagedSuspend(S))
      return StmtError();
  }
  return S;
}

void Sema::ActOnCppshStagedError(CppshStagedDecl *SD) {
  if (CppshStagedScopes.empty() || CppshStagedScopes.back().Decl != SD)
    return;
  CppshStagedScopes.pop_back();
  PopDeclContext();
}

Sema::CppshStagedScope *Sema::getCppshStagedJumpScope() {
  if (CppshStagedScopes.empty())
    return nullptr;
  for (DeclContext *DC = CurContext; DC; DC = DC->getParent()) {
    if (isa<CppshStagedDecl>(DC))
      return DC == CppshStagedScopes.back().Decl ? &CppshStagedScopes.back()
                                                 : nullptr;
    if (isa<CXXExpansionStmtDecl>(DC))
      continue;
    // A lambda's, a block's, a class's: its own jumps.
    return nullptr;
  }
  return nullptr;
}

StmtResult Sema::ActOnCppshStagedLeave(SourceLocation Loc, Scope *Target,
                                       bool IsContinue) {
  CppshStagedScope *Info = getCppshStagedJumpScope();
  if (!Info || !Info->BodyScope || !Target)
    return StmtEmpty();
  for (Scope *S = Info->BodyScope; S; S = S->getParent()) {
    if (S != Target)
      continue;
    Info->Leaves |= IsContinue ? CppshStagedStmt::LeavesByContinue
                               : CppshStagedStmt::LeavesByBreak;
    return new (Context) CppshStagedExitStmt(
        IsContinue ? CppshStagedExitStmt::Continue : CppshStagedExitStmt::Break,
        Loc, /*Value=*/nullptr, /*Slot=*/nullptr, /*Leave=*/nullptr);
  }
  return StmtEmpty();
}

StmtResult Sema::ActOnCppshStagedReturn(CppshStagedScope &Info,
                                        SourceLocation Loc, Expr *Value,
                                        Scope *CurScope) {
  Info.Leaves |= CppshStagedStmt::LeavesByReturn;
  // A value whose type is known only as the function runs, returned from a
  // function whose type is deduced from it: the function is a staged one --
  // this code its rest, its result kept for its caller.
  //
  // (In a template, a return of a type-dependent value deduces the type as
  // dependent -- the statement's first parse may have done so: not deduced
  // all the same.)
  if (!Info.KeepsResult && Value && Value->isTypeDependent())
    if (FunctionDecl *FD = getCurFunctionDecl(/*AllowLambda=*/true);
        FD && (FD->getReturnType()->isUndeducedType() ||
               (FD->getDeclaredReturnType()->getContainedAutoType() &&
                FD->getReturnType()->isDependentType())))
      Info.KeepsResult = true;
  // The function a staged one -- found so as it is parsed, or as a template
  // is instantiated (a value its returns depend on known only then): its
  // calls wait for the result it keeps.
  if (Info.KeepsResult)
    if (FunctionDecl *FD = getCurFunctionDecl(/*AllowLambda=*/true))
      CppshCutFunctions.insert(FD->getCanonicalDecl());
  // The rest of a staged function's body: what it returns is kept for the
  // function's caller, of its own type -- not the function's.
  if (Info.KeepsResult) {
    if (Value) {
      ExprResult R = ActOnFinishFullExpr(Value, Loc, /*DiscardedValue=*/false);
      if (R.isInvalid())
        return StmtError();
      Value = R.get();
    }
    return new (Context) CppshStagedExitStmt(CppshStagedExitStmt::Return, Loc,
                                             Value, nullptr, nullptr);
  }
  // A return of the function: checked, deduced from and converted as any.
  StmtResult R = BuildReturnStmt(Loc, Value, /*AllowRecovery=*/true);
  if (R.isInvalid())
    return R;
  auto *RS = dyn_cast<ReturnStmt>(R.get());
  if (!RS)
    return R;
  // Its value is constructed where the function returns it, by code compiled
  // later: no other object of the function may be constructed there (NRVO).
  if (RS->getNRVOCandidate())
    RS->setNRVOCandidate(nullptr);
  if (CurScope)
    CurScope->updateNRVOCandidate(nullptr);
  return new (Context) CppshStagedExitStmt(CppshStagedExitStmt::Return, Loc,
                                           RS->getRetValue(), nullptr, nullptr);
}

StmtResult Sema::BuildCppshStagedExit(unsigned K, SourceLocation Loc,
                                      Expr *Value, unsigned Target) {
  auto Kind = static_cast<CppshStagedExitStmt::ExitKind>(K);
  // Still in a staged statement's body (an enclosing template's
  // instantiation; a nested statement's, as the one around it is
  // instantiated): leaving that one.
  if (CppshStagedScope *Info = getCppshStagedJumpScope()) {
    if (Kind == CppshStagedExitStmt::Return && Info->Suspends) {
      Info->Leaves |= CppshStagedStmt::LeavesByReturn;
      return new (Context) CppshStagedExitStmt(Kind, Loc, Value, nullptr, nullptr);
    }
    if (Kind == CppshStagedExitStmt::Return)
      return ActOnCppshStagedReturn(*Info, Loc, Value, /*CurScope=*/nullptr);
    Info->Leaves |= Kind == CppshStagedExitStmt::Break
                        ? CppshStagedStmt::LeavesByBreak
                        : CppshStagedStmt::LeavesByContinue;
    return new (Context) CppshStagedExitStmt(Kind, Loc, nullptr, nullptr, nullptr);
  }
  // The body compiled as it runs: its function returns how it left.
  CppshStagedRun *Run = CurrentCppshStagedRun;
  if (!Run)
    return StmtError();
  ASTContext &C = Context;
  auto Leave = [&](unsigned Code) -> Stmt * {
    Expr *Lit = IntegerLiteral::Create(
        C, llvm::APInt(C.getIntWidth(C.IntTy), Code), C.IntTy, Loc);
    if (Run->Coroutine) {
      StmtResult R = BuildCoreturnStmt(Loc, Lit, /*IsImplicit=*/true);
      return R.isUsable() ? R.get() : nullptr;
    }
    return ReturnStmt::Create(C, Loc, Lit, /*NRVOCandidate=*/nullptr);
  };
  // A co_return of the code, compiled as a coroutine: the outer coroutine's
  // own -- its promise's return_value (or return_void) -- then the code's
  // way out.
  if (Kind == CppshStagedExitStmt::Return && Run->Coroutine) {
    if (!Run->OuterPromise)
      return StmtError();
    ExprResult Ptr = DefaultLvalueConversion(BuildDeclRefExpr(
        Run->OuterPromise, Run->OuterPromise->getType(), VK_LValue, Loc));
    ExprResult Promise =
        Ptr.isUsable() ? CreateBuiltinUnaryOp(Loc, UO_Deref, Ptr.get()) : ExprError();
    if (!Promise.isUsable())
      return StmtError();
    const bool HasValue = Value && !Value->getType()->isVoidType();
    CXXScopeSpec SS;
    DeclarationNameInfo Name(
        &PP.getIdentifierTable().get(HasValue ? "return_value" : "return_void"), Loc);
    ExprResult Member = BuildMemberReferenceExpr(
        Promise.get(), Promise.get()->getType(), Loc, /*IsArrow=*/false, SS,
        SourceLocation(), nullptr, Name, nullptr, nullptr);
    SmallVector<Expr *, 1> Args;
    if (HasValue)
      Args.push_back(Value);
    ExprResult Call = Member.isUsable()
                          ? BuildCallExpr(nullptr, Member.get(), Loc, Args, Loc)
                          : ExprError();
    if (Call.isUsable())
      Call = ActOnFinishFullExpr(Call.get(), Loc, /*DiscardedValue=*/true);
    Stmt *Out = Leave(Kind);
    if (!Call.isUsable() || !Out)
      return StmtError();
    // A void expression co_returned: evaluated first.
    if (Value && !HasValue) {
      ExprResult V = ActOnFinishFullExpr(Value, Loc, /*DiscardedValue=*/true);
      if (V.isUsable()) {
        ExprResult Both = BuildBinOp(nullptr, Loc, BO_Comma, V.get(), Call.get());
        if (Both.isUsable())
          Call = Both;
      }
    }
    return new (C) CppshStagedExitStmt(Kind, Loc, Call.get(), nullptr, Out);
  }
  if (Kind != CppshStagedExitStmt::Return)
    return new (C) CppshStagedExitStmt(
        Kind, Loc, nullptr, nullptr,
        Leave(Kind == CppshStagedExitStmt::Goto ? 4 + Target : unsigned(Kind)),
        Target);
  // A staged function's result: of the type its returns give it (as an
  // `auto` function's would be), constructed where the interpreter keeps it.
  QualType R = Run->ReturnType;
  if (Run->KeepsResult) {
    QualType T;
    if (Value && !Value->getType()->isVoidType()) {
      T = Value->getType().getNonReferenceType().getUnqualifiedType();
      if (T->isArrayType())
        T = C.getArrayDecayedType(T);
      else if (T->isFunctionType())
        T = C.getPointerType(T);
    }
    if (!T.isNull()) {
      if (Run->ReturnType.isNull()) {
        Run->ReturnType = T;
      } else if (!C.hasSameType(Run->ReturnType, T)) {
        Diag(Loc, diag::err_auto_fn_different_deductions)
            << 0 << T << Run->ReturnType;
        return StmtError();
      }
    }
    R = T;
  }
  if (R.isNull() || R->isVoidType()) {
    if (Value) {
      ExprResult V = ActOnFinishFullExpr(Value, Loc, /*DiscardedValue=*/true);
      if (V.isInvalid())
        return StmtError();
      Value = V.get();
    }
    return new (C) CppshStagedExitStmt(Kind, Loc, Value, nullptr, Leave(Kind));
  }
  if (!Value || !Run->Slot)
    return StmtError();
  // The value, constructed where the function around the statement returns
  // it: initialized as its result.
  ExprResult Init = PerformCopyInitialization(
      InitializedEntity::InitializeResult(Loc, R), Loc, Value);
  if (Init.isInvalid())
    return StmtError();
  Init = ActOnFinishFullExpr(Init.get(), Loc, /*DiscardedValue=*/false);
  if (Init.isInvalid())
    return StmtError();
  ExprResult Slot = DefaultLvalueConversion(BuildDeclRefExpr(
      Run->Slot, Run->Slot->getType(), VK_LValue, Loc));
  if (Slot.isInvalid())
    return StmtError();
  return new (C)
      CppshStagedExitStmt(Kind, Loc, Init.get(), Slot.get(), Leave(Kind));
}

CppshStagedDecl *
Sema::ActOnStartCppshStagedInstantiation(CppshStagedDecl *Old,
                                         ArrayRef<QualType> Types,
                                         bool KeepsResult) {
  auto *SD = CppshStagedDecl::Create(Context, CurContext, Old->getLocation());
  CurContext->addDecl(SD);
  SD->setUsesThis(Old->usesThis());
  ArrayRef<ImplicitParamDecl *> OldParams = Old->parameters();
  // The result's type, its depth as the instantiation leaves it.
  if (Old->getResultTypeParm() && !Types.empty())
    if (const auto *TT = Types.back()->getAs<TemplateTypeParmType>())
      SD->setResultTypeParm(TemplateTypeParmDecl::Create(
          Context, Context.getTranslationUnitDecl(), Old->getLocation(),
          Old->getLocation(), TT->getDepth(), TT->getIndex(), /*Id=*/nullptr,
          /*Typename=*/true, /*ParameterPack=*/false));
  SmallVector<ImplicitParamDecl *, 8> Params;
  for (unsigned I = 0; I < OldParams.size() && I < Types.size(); ++I) {
    auto *P = ImplicitParamDecl::Create(
        Context, SD, OldParams[I]->getLocation(), OldParams[I]->getIdentifier(),
        Types[I], ImplicitParamKind::CppshStaged);
    SD->addDecl(P);
    Params.push_back(P);
  }
  SD->setParameters(Context, Params);
  SD->setSuspends(Old->suspends());
  CppshStagedScope Info;
  Info.Decl = SD;
  Info.KeepsResult = KeepsResult;
  Info.Outer = CurContext;
  Info.Suspends = Old->suspends();
  CppshStagedScopes.push_back(std::move(Info));
  CurContext = SD;
  return SD;
}

StmtResult Sema::ActOnFinishCppshStagedInstantiation(
    CppshStagedDecl *SD, StmtResult Body, ArrayRef<Expr *> Frame,
    CppshStagedStmt *Old, ArrayRef<LabelDecl *> Targets) {
  if (CppshStagedScopes.empty() || CppshStagedScopes.back().Decl != SD)
    return StmtError();
  CppshStagedScope Info = CppshStagedScopes.pop_back_val();
  CurContext = Info.Outer;
  if (Body.isInvalid() || !Body.get())
    return StmtError();
  auto *S = CppshStagedStmt::Create(
      Context, SD, Body.get(), Frame, Old->getLeaves() | Info.Leaves,
      Old->keepsResult() || Info.KeepsResult, Old->getBeginLoc(),
      Old->getEndLoc());
  // In staged code compiled as it runs, directly in its function: a label
  // outside that code too is reached by that function's leaving for it.
  SmallVector<int, 4> Propagate(Targets.size(), -1);
  if (CurrentCppshStagedRun && CurrentCppshStagedRun->Staged &&
      CppshStagedScopes.empty()) {
    ArrayRef<LabelDecl *> Outer = CurrentCppshStagedRun->Staged->gotoTargets();
    for (unsigned I = 0; I < Targets.size(); ++I)
      if (const auto *It = llvm::find(Outer, Targets[I]); It != Outer.end())
        Propagate[I] = 4 + (It - Outer.begin());
  }
  S->setGotoTargets(Context, Targets, Propagate);
  S->setEntries(Context, cppshEntriesOf(Body.get()));
  SD->setStagedStmt(S);
  if (SD->suspends() || Info.Suspends) {
    SD->setSuspends(true);
    if (!BuildCppshStagedSuspend(S))
      return StmtError();
  }
  return S;
}

StmtResult Sema::InstantiateCppshStaged(CppshStagedStmt *S,
                                        ArrayRef<VarDecl *> Locals,
                                        QualType ResultType,
                                        CppshStagedRun &Run) {
  CppshStagedDecl *SD = S ? S->getStagedDecl() : nullptr;
  if (!SD || Locals.size() != SD->parameters().size())
    return StmtError();
  ArrayRef<ImplicitParamDecl *> Params = SD->parameters();
  CppshStagedRun *SavedRun = std::exchange(CurrentCppshStagedRun, &Run);
  SmallVector<CppshStagedScope, 2> SavedScopes = std::move(CppshStagedScopes);
  CppshStagedScopes.clear();
  auto Restore = llvm::scope_exit([&] {
    CurrentCppshStagedRun = SavedRun;
    CppshStagedScopes = std::move(SavedScopes);
  });
  // The type of the staged function's result, now known.
  MultiLevelTemplateArgumentList Args;
  if (TemplateTypeParmDecl *T = SD->getResultTypeParm()) {
    if (ResultType.isNull())
      return StmtError();
    TemplateArgument Arg(ResultType);
    Args = MultiLevelTemplateArgumentList(SD, Arg, /*Final=*/true);
    Args.addOuterRetainedLevels(T->getDepth());
  }
  // Each staged parameter, the local it stands for (its value known); the
  // context, the function the body is compiled into.
  LocalInstantiationScope Scope(*this);
  Scope.InstantiatedLocal(SD, cast<Decl>(CurContext));
  for (unsigned I = 0; I < Params.size(); ++I)
    Scope.InstantiatedLocal(Params[I], Locals[I]);
  // Each run-time template argument the body uses implicitly (a default):
  // the local holding its value.
  auto SavedSupplies = CppshSuppliedExprs;
  auto RestoreSupplies =
      llvm::scope_exit([&] { CppshSuppliedExprs = std::move(SavedSupplies); });
  for (const auto &[Loc, Index] : SD->supplies())
    if (Index < Locals.size())
      CppshSuppliedExprs[Loc.getRawEncoding()] = BuildDeclRefExpr(
          Locals[Index], Locals[Index]->getType().getNonReferenceType(),
          VK_LValue, Loc);
  // A label outside the body it jumps to: that same label (its function
  // leaves for it).
  for (LabelDecl *L : S->gotoTargets())
    Scope.InstantiatedLocal(L, L);
  Run.EntryLabels.assign(S->entries().size(), nullptr);
  NonSFINAEContext NonSFINAE(*this);
  InstantiatingTemplate Inst(*this, S->getBeginLoc(), S, S->getSourceRange());
  if (Inst.isInvalid())
    return StmtError();
  StmtResult Body = SubstStmt(S->getBody(), Args);
  if (Body.isInvalid())
    return Body;
  // Its last statement's value shown (the last of an input, its `;` not
  // written): as the interpreter shows any.
  if (S->printsValue() && Run.PrintValue)
    if (auto *C = dyn_cast<CompoundStmt>(Body.get()); C && !C->body_empty())
      if (auto *Last = dyn_cast<Expr>(C->body_back()))
        if (Expr *Shown = Run.PrintValue(Last))
          C->body_begin()[C->size() - 1] = Shown;
  // Entered elsewhere than at its start: `if (entry == I + 1) goto L;` for
  // each entry, L the label it is in the body compiled -- a label's own
  // instantiation, a case's made of it (ActOnCppshStagedEntry).
  SmallVector<Stmt *, 8> Stmts;
  ArrayRef<Stmt *> Entries = S->entries();
  for (unsigned I = 0; I < Entries.size() && Run.Entry; ++I) {
    LabelDecl *L = Run.EntryLabels[I];
    if (const auto *LS = dyn_cast<LabelStmt>(Entries[I]))
      if (auto *Found = Scope.getInstantiationOfIfExists(LS->getDecl()))
        if (Decl *D = dyn_cast<Decl *>(*Found))
          L = dyn_cast<LabelDecl>(D);
    if (!L)
      continue;
    const SourceLocation Loc = cppshEntryLoc(Entries[I]);
    ExprResult Entry = DefaultLvalueConversion(
        BuildDeclRefExpr(Run.Entry, Run.Entry->getType(), VK_LValue, Loc));
    Expr *Index = IntegerLiteral::Create(
        Context, llvm::APInt(Context.getIntWidth(Context.IntTy), I + 1),
        Context.IntTy, Loc);
    ExprResult Cond = Entry.isUsable()
                          ? CreateBuiltinBinOp(Loc, BO_EQ, Entry.get(), Index)
                          : ExprError();
    ConditionResult C = Cond.isUsable()
                            ? ActOnCondition(nullptr, Loc, Cond.get(),
                                             ConditionKind::Boolean)
                            : ConditionError();
    if (C.isInvalid())
      return StmtError();
    L->markUsed(Context);
    Stmt *Goto = new (Context) GotoStmt(L, Loc, Loc);
    StmtResult If = ActOnIfStmt(Loc, IfStatementKind::Ordinary, Loc, nullptr, C,
                                Loc, Goto, SourceLocation(), nullptr);
    if (If.isUsable())
      Stmts.push_back(If.get());
  }
  if (Stmts.empty())
    return Body;
  Stmts.push_back(Body.get());
  return CompoundStmt::Create(Context, Stmts, FPOptionsOverride(),
                              S->getBeginLoc(), S->getEndLoc());
}

StmtResult Sema::ActOnCppshStagedEntry(SourceLocation Loc, Stmt *SubStmt) {
  CppshStagedRun *Run = CurrentCppshStagedRun;
  if (!Run || !Run->Staged || !getCurFunction() ||
      !getCurFunction()->SwitchStack.empty())
    return StmtEmpty();
  // A label of its own, in the function compiled; jumped to as the body is
  // entered there (from the statement's entries, where it is one of them).
  auto *L = LabelDecl::Create(Context, CurContext, Loc,
                              &PP.getIdentifierTable().get("__cppsh_entry"));
  auto *LS = new (Context) LabelStmt(Loc, L, SubStmt);
  L->setStmt(LS);
  if (!getCppshStagedJumpScope()) {
    ArrayRef<Stmt *> Entries = Run->Staged->entries();
    for (unsigned I = 0; I < Entries.size() && I < Run->EntryLabels.size(); ++I)
      if (isa<SwitchCase>(Entries[I]) && cppshEntryLoc(Entries[I]) == Loc)
        Run->EntryLabels[I] = L;
  }
  return LS;
}

// std::sh's declaration of that name.
static NamedDecl *cppshShDecl(Sema &S, StringRef Name) {
  NamespaceDecl *Std = S.getStdNamespace();
  if (!Std)
    return nullptr;
  LookupResult ShR(S, &S.PP.getIdentifierTable().get("sh"), SourceLocation(),
                   Sema::LookupNamespaceName);
  S.LookupQualifiedName(ShR, Std);
  auto *Sh = ShR.getAsSingle<NamespaceDecl>();
  if (!Sh)
    return nullptr;
  LookupResult R(S, &S.PP.getIdentifierTable().get(Name), SourceLocation(),
                 Sema::LookupOrdinaryName);
  S.LookupQualifiedName(R, Sh);
  for (NamedDecl *D : R)
    return D->getUnderlyingDecl();
  return nullptr;
}

// In a coroutine: the code's frame, its state and how it left, and the loop
// awaiting its steps --
//   void *__cppsh_frame[] = {(void *)&local..., nullptr};
//   std::sh::__cppsh_staged_state __cppsh_state{node, __cppsh_frame, 0};
//   int __cppsh_left = -1;
//   while ((__cppsh_left = co_await std::sh::__cppsh_staged_step<P>{
//             __cppsh_state, <the promise>}) < 0) ;
bool Sema::BuildCppshStagedSuspend(CppshStagedStmt *SS) {
  ASTContext &C = Context;
  const SourceLocation Loc = SS->getBeginLoc();
  sema::FunctionScopeInfo *FSI = getCurFunction();
  if (!FSI)
    return false;
  if (!FSI->CoroutinePromise &&
      !ActOnCoroutineBodyStart(getCurScope(), Loc, "co_await"))
    return false;
  VarDecl *Promise = FSI->CoroutinePromise;
  auto *StateD = dyn_cast_or_null<TypeDecl>(cppshShDecl(*this, "__cppsh_staged_state"));
  auto *StepT = dyn_cast_or_null<ClassTemplateDecl>(cppshShDecl(*this, "__cppsh_staged_step"));
  if (!Promise || !StateD || !StepT)
    return false;
  auto MakeVar = [&](llvm::StringRef Name, QualType T) {
    auto *V = VarDecl::Create(C, CurContext, Loc, Loc, &PP.getIdentifierTable().get(Name),
                              T, C.getTrivialTypeSourceInfo(T, Loc), SC_None);
    V->setImplicit();
    return V;
  };
  auto Ref = [&](VarDecl *V) {
    return BuildDeclRefExpr(V, V->getType().getNonReferenceType(), VK_LValue, Loc);
  };
  auto VoidPtr = [&](Expr *E) -> Expr * {
    ExprResult R = BuildCStyleCastExpr(Loc, C.getTrivialTypeSourceInfo(C.VoidPtrTy, Loc),
                                       Loc, E);
    return R.isUsable() ? R.get() : nullptr;
  };
  SmallVector<Stmt *, 4> Stmts;
  // The frame: each local's address; `this`; a staged call made, no address.
  SmallVector<Expr *, 8> Entries;
  for (Expr *E : SS->frame()) {
    Expr *Entry = nullptr;
    if (E->isGLValue()) {
      ExprResult Addr = CreateBuiltinUnaryOp(Loc, UO_AddrOf, E);
      Entry = Addr.isUsable() ? VoidPtr(Addr.get()) : nullptr;
    } else if (E->getType()->isPointerType()) {
      Entry = VoidPtr(E);
    } else {
      ExprResult Null = ActOnCXXNullPtrLiteral(Loc);
      ExprResult Both = Null.isUsable()
                            ? BuildBinOp(nullptr, Loc, BO_Comma, E, VoidPtr(Null.get()))
                            : ExprError();
      Entry = Both.isUsable() ? Both.get() : nullptr;
    }
    if (!Entry)
      return false;
    Entries.push_back(Entry);
  }
  ExprResult Null = ActOnCXXNullPtrLiteral(Loc);
  if (!Null.isUsable())
    return false;
  Entries.push_back(VoidPtr(Null.get()));
  const QualType FrameT = C.getConstantArrayType(
      C.VoidPtrTy, llvm::APInt(32, Entries.size()), nullptr,
      ArraySizeModifier::Normal, 0);
  VarDecl *FrameV = MakeVar("__cppsh_frame", FrameT);
  ExprResult FrameInit = ActOnInitList(Loc, Entries, Loc);
  if (!FrameInit.isUsable())
    return false;
  AddInitializerToDecl(FrameV, FrameInit.get(), /*DirectInit=*/false);
  // The state: the statement itself (in this process), the frame, entered
  // at its start.
  VarDecl *StateV = MakeVar("__cppsh_state", C.getTypeDeclType(StateD));
  Expr *Node = IntegerLiteral::Create(
      C, llvm::APInt(64, reinterpret_cast<uintptr_t>(SS)), C.UnsignedLongLongTy, Loc);
  ExprResult NodePtr = BuildCStyleCastExpr(
      Loc, C.getTrivialTypeSourceInfo(C.getPointerType(C.VoidTy.withConst()), Loc), Loc,
      Node);
  if (!NodePtr.isUsable())
    return false;
  Expr *StateArgs[] = {NodePtr.get(), Ref(FrameV),
                       IntegerLiteral::Create(C, llvm::APInt(C.getIntWidth(C.IntTy), 0),
                                              C.IntTy, Loc)};
  ExprResult StateInit = ActOnInitList(Loc, StateArgs, Loc);
  if (!StateInit.isUsable())
    return false;
  AddInitializerToDecl(StateV, StateInit.get(), /*DirectInit=*/false);
  VarDecl *LeftV = MakeVar("__cppsh_left", C.IntTy);
  AddInitializerToDecl(
      LeftV,
      IntegerLiteral::Create(C, llvm::APInt(C.getIntWidth(C.IntTy), -1, true), C.IntTy, Loc),
      /*DirectInit=*/false);
  for (VarDecl *V : {FrameV, StateV, LeftV}) {
    if (V->isInvalidDecl())
      return false;
    StmtResult DS = ActOnDeclStmt(ConvertDeclToDeclGroup(V), Loc, Loc);
    if (!DS.isUsable())
      return false;
    Stmts.push_back(DS.get());
  }
  // The step: std::sh::__cppsh_staged_step<P>{state, promise}, awaited.
  TemplateArgumentListInfo Args(Loc, Loc);
  const QualType PromiseT = Promise->getType();
  Args.addArgument(TemplateArgumentLoc(TemplateArgument(PromiseT),
                                       C.getTrivialTypeSourceInfo(PromiseT, Loc)));
  const QualType Step = CheckTemplateIdType(ElaboratedTypeKeyword::None,
                                            TemplateName(StepT), Loc, Args,
                                            getCurScope(), false);
  if (Step.isNull())
    return false;
  // Its braced list, as the parser makes one: what a list-initialization
  // takes (the one InitListExpr, not its elements).
  Expr *StepArgs[] = {Ref(StateV), Ref(Promise)};
  ExprResult StepList = ActOnInitList(Loc, StepArgs, Loc);
  if (!StepList.isUsable())
    return false;
  Expr *StepInit[] = {StepList.get()};
  ExprResult StepE = BuildCXXTypeConstructExpr(C.getTrivialTypeSourceInfo(Step, Loc),
                                               Loc, StepInit, Loc,
                                               /*ListInitialization=*/true);
  ExprResult Await =
      StepE.isUsable() ? ActOnCoawaitExpr(getCurScope(), Loc, StepE.get()) : ExprError();
  ExprResult Assign = Await.isUsable()
                          ? BuildBinOp(getCurScope(), Loc, BO_Assign, Ref(LeftV), Await.get())
                          : ExprError();
  ExprResult Less =
      Assign.isUsable()
          ? BuildBinOp(getCurScope(), Loc, BO_LT, Assign.get(),
                       IntegerLiteral::Create(C, llvm::APInt(C.getIntWidth(C.IntTy), 0),
                                              C.IntTy, Loc))
          : ExprError();
  ConditionResult Cond = Less.isUsable()
                             ? ActOnCondition(getCurScope(), Loc, Less.get(),
                                              ConditionKind::Boolean)
                             : ConditionError();
  if (Cond.isInvalid())
    return false;
  StmtResult Loop = ActOnWhileStmt(Loc, Loc, Cond, Loc, new (C) NullStmt(Loc));
  if (!Loop.isUsable())
    return false;
  Stmts.push_back(Loop.get());
  ExprResult Left = DefaultLvalueConversion(Ref(LeftV));
  if (!Left.isUsable())
    return false;
  SS->setSuspend(CompoundStmt::Create(C, Stmts, FPOptionsOverride(), Loc, Loc),
                 Left.get());
  return true;
}

Expr *Sema::CppshStagedThis(SourceLocation Loc) {
  CppshStagedRun *Run = CurrentCppshStagedRun;
  if (!Run || !Run->This || !Run->Function ||
      getFunctionLevelDeclContext() != Run->Function)
    return nullptr;
  ExprResult R = DefaultLvalueConversion(
      BuildDeclRefExpr(Run->This, Run->This->getType(), VK_LValue, Loc));
  return R.isUsable() ? R.get() : nullptr;
}
