//===--------- IncrementalParser.cpp - Incremental Compilation  -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the class which performs incremental code compilation.
//
//===----------------------------------------------------------------------===//

#include "IncrementalParser.h"
#include "IncrementalAction.h"

#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclContextInternals.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/CodeGen/ModuleBuilder.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Interpreter/PartialTranslationUnit.h"
#include "clang/Parse/Parser.h"
#include "clang/Sema/CppshStaging.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/Sema.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CrashRecoveryContext.h"
#include "llvm/Support/Error.h"

#include <sstream>

#define DEBUG_TYPE "clang-repl"

namespace clang {

// cppsh: where each top-level declaration of the input being parsed starts --
// where the interpreter may stage it (Interpreter::ParseAndExecute).
std::vector<SourceLocation> CppshTopLevelStarts;

// What the consumer was handed while the input had an error, and did not
// pass on to code generation (IncrementalAction): given to it again once the
// failed input is taken back, but for the decls of that input itself.
std::vector<Decl *> CppshDroppedDecls;
extern bool CppshTopNeed;
extern SourceLocation CppshHoistBegin, CppshHoistEnd;
extern bool CppshInHoist;

// IncrementalParser::IncrementalParser() {}

IncrementalParser::IncrementalParser(CompilerInstance &Instance,
                                     IncrementalAction *Act, llvm::Error &Err,
                                     std::list<PartialTranslationUnit> &PTUs)
    : S(Instance.getSema()), Act(Act), PTUs(PTUs) {
  llvm::ErrorAsOutParameter EAO(&Err);
  Consumer = &S.getASTConsumer();
  P.reset(new Parser(S.getPreprocessor(), S, /*SkipBodies=*/false));
  // cppsh: every token of what the user types, recorded once.
  S.getPreprocessor().setTokenWatcher(
      [&SM = S.getSourceManager()](const Token &T) { cppshRecordToken(SM, T); });

  if (ExternalASTSource *External = S.getASTContext().getExternalSource())
    External->StartTranslationUnit(Consumer);

  P->Initialize();
}

IncrementalParser::~IncrementalParser() { P.reset(); }

void IncrementalParser::StartPTU() {
  // Add a new PTU.
  ASTContext &C = S.getASTContext();
  C.addTranslationUnitDecl();

  // Skip previous eof due to last incremental input.
  const bool AtEof = P->getCurToken().is(tok::eof);
  if (AtEof)
    P->ConsumeAnyToken();
  // A new PTU's scope -- after an input, or between two top-level
  // declarations of one (each a unit of its own: ParseNextTopLevel).
  // FIXME: Clang does not call ExitScope on finalizing the regular TU, we
  // might want to do that around HandleEndOfTranslationUnit.
  if (AtEof || StepwiseInput) {
    P->ExitScope();
    S.CurContext = nullptr;
    P->EnterScope(Scope::DeclScope);
    S.ActOnTranslationUnitScope(P->getCurScope());
  }
  CppshDroppedDecls.clear();
  ConsumerFailed = false;
  // What it uses and nothing defines, from here on its own.
  UndefinedUsedAtStart = S.UndefinedButUsed.size();
}

// A failed input taken back whole: its decls out of the AST, the module code
// generation was building for it thrown away (with what it took out of the
// deferred decls put back, and its own forgotten), the diagnostics reset, and
// what was not code generated while it had an error handed over again.
llvm::Error IncrementalParser::TakeBackPTU(llvm::StringRef Why) {
  TranslationUnitDecl *TU = S.getASTContext().getTranslationUnitDecl();
  if (CodeGenerator *CG = Act->getCodeGen())
    CG->DiscardIncrementalUnit(TU, /*ThrowModuleAway=*/true);
  CleanUpPTU(TU);
  // The translation-unit scope, and Sema's context, named the unit just
  // withdrawn: the one now current, so that what is parsed or built next
  // (a snapshot's unit before the next input) looks names up in a live one.
  if (S.TUScope && S.TUScope == P->getCurScope()) {
    S.CurContext = nullptr;
    S.ActOnTranslationUnitScope(S.TUScope);
  }
  // Its uses of what nothing defines gone with it: no warning of them.
  while (S.UndefinedButUsed.size() > UndefinedUsedAtStart)
    S.UndefinedButUsed.pop_back();
  DiagnosticsEngine &Diags = S.getDiagnostics();
  Diags.Reset(/*soft=*/true);
  Diags.getClient()->clear();
  std::vector<Decl *> Dropped = std::exchange(CppshDroppedDecls, {});
  for (Decl *D : Dropped)
    if (D->getTranslationUnitDecl() != TU)
      Consumer->HandleTopLevelDecl(DeclGroupRef(D));
  return llvm::make_error<llvm::StringError>(Why, std::error_code());
}

llvm::Expected<TranslationUnitDecl *> IncrementalParser::FinishPTU(
    Sema::LocalEagerInstantiationScope &LocalInstantiations,
    Sema::GlobalEagerInstantiationScope &GlobalInstantiations) {
  if (ConsumerFailed)
    return TakeBackPTU("Parsing failed. The consumer rejected a decl");
  DiagnosticsEngine &Diags = S.getDiagnostics();
  if (Diags.hasErrorOccurred())
    return TakeBackPTU("Parsing failed.");
  // A run-time template argument at the top level, a staged function's call
  // there: taken back, to be parsed again once it ran
  // (Interpreter::cppshStageDecl).
  if (CppshTopNeed)
    return TakeBackPTU("cppsh: a top-level run-time template argument");
  if (StepwiseInput && CppshHoistBegin.isValid() && CppshHoistEnd.isValid() &&
      !CppshInHoist)
    return TakeBackPTU("cppsh: a staged function's call at the top level");

  // Process any TopLevelDecls generated by #pragma weak.
  for (Decl *D : S.WeakTopLevelDecls()) {
    DeclGroupRef DGR(D);
    Consumer->HandleTopLevelDecl(DGR);
  }

  LocalInstantiations.perform();
  GlobalInstantiations.perform();

  ASTContext &C = S.getASTContext();
  Consumer->HandleTranslationUnit(C);

  // An error the instantiations at the end of the input raised: code
  // generation dropped its module for it (HandleTranslationUnit), and the
  // input is taken back as any failed one.
  if (Diags.hasErrorOccurred())
    return TakeBackPTU("Parsing failed.");

  return C.getTranslationUnitDecl();
}

llvm::Expected<TranslationUnitDecl *>
IncrementalParser::ParseOrWrapTopLevelDecl() {
  // Recover resources if we crash before exiting this method.
  llvm::CrashRecoveryContextCleanupRegistrar<Sema> CleanupSema(&S);
  Sema::GlobalEagerInstantiationScope GlobalInstantiations(S, /*Enabled=*/true,
                                                           /*AtEndOfTU=*/true);
  Sema::LocalEagerInstantiationScope LocalInstantiations(S, /*AtEndOfTU=*/true);
  StartPTU();

  Parser::DeclGroupPtrTy ADecl;
  Sema::ModuleImportState ImportState;
  CppshTopLevelStarts.clear();
  CppshTopLevelStarts.push_back(P->getCurToken().getLocation());
  for (bool AtEOF = P->ParseFirstTopLevelDecl(ADecl, ImportState); !AtEOF;
       CppshTopLevelStarts.push_back(P->getCurToken().getLocation()),
            AtEOF = P->ParseTopLevelDecl(ADecl, ImportState)) {
    if (ADecl && !Consumer->HandleTopLevelDecl(ADecl.get()))
      return TakeBackPTU("Parsing failed. The consumer rejected a decl");
  }
  return FinishPTU(LocalInstantiations, GlobalInstantiations);
}

llvm::Error IncrementalParser::BeginBuild() {
  if (BuildGlobalInstantiations)
    return llvm::make_error<llvm::StringError>(
        "cppsh: a unit is being built already", std::error_code());
  BuildGlobalInstantiations.emplace(S, /*Enabled=*/true, /*AtEndOfTU=*/true);
  BuildLocalInstantiations.emplace(S, /*AtEndOfTU=*/true);
  StartPTU();
  return llvm::Error::success();
}

void IncrementalParser::AddBuilt(DeclGroupRef DG) {
  if (!Consumer->HandleTopLevelDecl(DG))
    ConsumerFailed = true;
}

llvm::Expected<TranslationUnitDecl *> IncrementalParser::EndBuild() {
  // A unit built from the AST, not parsed: its instantiations run in the
  // translation unit's scope, naming this unit -- what they look up
  // unqualified is the templates' own (and argument-dependent), but Sema
  // still asks the scope of some (a range-for numbers the variables it
  // invents by its depth): never a scope of a parse, nor none.
  Scope *const SavedScope = S.getCurScope();
  if (S.TUScope)
    S.TUScope->setEntity(S.getASTContext().getTranslationUnitDecl());
  S.setCurScopeForBuiltUnit(S.TUScope);
  llvm::Expected<TranslationUnitDecl *> TU =
      FinishPTU(*BuildLocalInstantiations, *BuildGlobalInstantiations);
  S.setCurScopeForBuiltUnit(SavedScope);
  BuildLocalInstantiations.reset();
  BuildGlobalInstantiations.reset();
  return TU;
}

llvm::Error IncrementalParser::BeginInput(llvm::StringRef input) {
  Preprocessor &PP = S.getPreprocessor();
  std::ostringstream SourceName;
  SourceName << "input_line_" << InputCount++;
  size_t InputSize = input.size();
  std::unique_ptr<llvm::MemoryBuffer> MB(
      llvm::WritableMemoryBuffer::getNewUninitMemBuffer(InputSize + 1,
                                                        SourceName.str()));
  char *MBStart = const_cast<char *>(MB->getBufferStart());
  memcpy(MBStart, input.data(), InputSize);
  MBStart[InputSize] = '\n';
  SourceManager &SM = S.getSourceManager();
  SourceLocation NewLoc = SM.getLocForStartOfFile(SM.getMainFileID());
  FileEntryRef FE = SM.getFileManager().getVirtualFileRef(
      SourceName.str(), InputSize, 0 /* mod time*/);
  SM.overrideFileContents(FE, std::move(MB));
  PP.getHeaderSearchInfo().getFileInfo(FE);
  FileID FID = SM.createFileID(FE, NewLoc, SrcMgr::C_User);
  if (PP.EnterSourceFile(FID, /*DirLookup=*/nullptr, NewLoc))
    return llvm::make_error<llvm::StringError>("Parsing failed. "
                                               "Cannot enter source file.",
                                               std::error_code());
  return llvm::Error::success();
}

llvm::Expected<TranslationUnitDecl *>
IncrementalParser::ParseNextTopLevel(bool First, bool &Done) {
  // The input's own eof: none left (the first one met is the last input's).
  Done = !First && P->getCurToken().is(tok::eof);
  if (Done)
    return nullptr;
  llvm::CrashRecoveryContextCleanupRegistrar<Sema> CleanupSema(&S);
  Sema::GlobalEagerInstantiationScope GlobalInstantiations(S, /*Enabled=*/true,
                                                           /*AtEndOfTU=*/true);
  Sema::LocalEagerInstantiationScope LocalInstantiations(S, /*AtEndOfTU=*/true);
  StepwiseInput = !First;
  StartPTU();
  StepwiseInput = true;
  Parser::DeclGroupPtrTy ADecl;
  Sema::ModuleImportState ImportState;
  CppshTopLevelStarts.clear();
  CppshTopLevelStarts.push_back(P->getCurToken().getLocation());
  const bool AtEOF = First ? P->ParseFirstTopLevelDecl(ADecl, ImportState)
                           : P->ParseTopLevelDecl(ADecl, ImportState);
  (void)AtEOF;
  // One to be taken back for its staging (FinishPTU): not handed to code
  // generation -- what it declares is not what it will be (a staged call's
  // result, void until it runs).
  const bool Staging =
      CppshTopNeed ||
      (CppshHoistBegin.isValid() && CppshHoistEnd.isValid() && !CppshInHoist);
  if (cppshTraceStaging())
    llvm::errs() << "cppsh-trace: top-level declaration "
                 << (!ADecl ? "none" : Staging ? "held back" : "handed to code generation")
                 << "\n";
  if (ADecl && !Staging && !Consumer->HandleTopLevelDecl(ADecl.get()))
    return TakeBackPTU("Parsing failed. The consumer rejected a decl");
  return FinishPTU(LocalInstantiations, GlobalInstantiations);
}

void IncrementalParser::SkipInput() {
  while (P->getCurToken().isNot(tok::eof))
    P->ConsumeAnyToken();
}

llvm::Expected<TranslationUnitDecl *>
IncrementalParser::Parse(llvm::StringRef input) {
  Preprocessor &PP = S.getPreprocessor();
  assert(PP.isIncrementalProcessingEnabled() && "Not in incremental mode!?");

  std::ostringstream SourceName;
  SourceName << "input_line_" << InputCount++;

  // Create an uninitialized memory buffer, copy code in and append "\n"
  size_t InputSize = input.size(); // don't include trailing 0
  // MemBuffer size should *not* include terminating zero
  std::unique_ptr<llvm::MemoryBuffer> MB(
      llvm::WritableMemoryBuffer::getNewUninitMemBuffer(InputSize + 1,
                                                        SourceName.str()));
  char *MBStart = const_cast<char *>(MB->getBufferStart());
  memcpy(MBStart, input.data(), InputSize);
  MBStart[InputSize] = '\n';

  SourceManager &SM = S.getSourceManager();

  // FIXME: Create SourceLocation, which will allow clang to order the overload
  // candidates for example
  SourceLocation NewLoc = SM.getLocForStartOfFile(SM.getMainFileID());

  // Create FileID for the current buffer.
  FileID FID;
  // Create FileEntry and FileID for the current buffer.
  FileEntryRef FE = SM.getFileManager().getVirtualFileRef(
      SourceName.str(), InputSize, 0 /* mod time*/);
  SM.overrideFileContents(FE, std::move(MB));

  // Ensure HeaderFileInfo exists before lookup to prevent assertion
  HeaderSearch &HS = PP.getHeaderSearchInfo();
  HS.getFileInfo(FE);

  FID = SM.createFileID(FE, NewLoc, SrcMgr::C_User);

  // NewLoc only used for diags.
  if (PP.EnterSourceFile(FID, /*DirLookup=*/nullptr, NewLoc))
    return llvm::make_error<llvm::StringError>("Parsing failed. "
                                               "Cannot enter source file.",
                                               std::error_code());

  auto PTU = ParseOrWrapTopLevelDecl();
  if (!PTU)
    return PTU.takeError();

  if (PP.getLangOpts().DelayedTemplateParsing) {
    // Microsoft-specific:
    // Late parsed templates can leave unswallowed "macro"-like tokens.
    // They will seriously confuse the Parser when entering the next
    // source file. So lex until we are EOF.
    Token Tok;
    do {
      PP.Lex(Tok);
    } while (Tok.isNot(tok::eof));
  } else {
    Token AssertTok;
    PP.Lex(AssertTok);
    assert(AssertTok.is(tok::eof) &&
           "Lexer must be EOF when starting incremental parse!");
  }

  return PTU;
}

void IncrementalParser::withdrawMostRecentTU(
    TranslationUnitDecl *MostRecentTU) {
  TranslationUnitDecl *Prev = MostRecentTU->getPreviousDecl();
  if (!Prev)
    return;
  assert(MostRecentTU->getMostRecentDecl() == MostRecentTU &&
         "Not the most recent translation unit!");

  // Rebuild A -> ... -> Prev -> MostRecentTU as A -> ... -> Prev.
  MostRecentTU->getFirstDecl()->RedeclLink.setLatest(Prev);

  // getTranslationUnitDecl() requires the active unit to be the latest one.
  ASTContext &C = S.getASTContext();
  if (C.TraversalScope.size() == 1 && C.TraversalScope.back() == MostRecentTU)
    C.TraversalScope = {Prev};
  C.TUDecl = Prev;
}

/// Removes decls introduced in the discarding PTU and restores the
/// redeclaration chain to previous state.
class ASTDeclUnmerger : public DeclVisitor<ASTDeclUnmerger> {
  Sema &S;
  TranslationUnitDecl *DiscardedTU;

  template <typename DeclT> void withdraw(Redeclarable<DeclT> *DBase) {
    if (NamedDecl *Prev = findSurvivor(static_cast<DeclT *>(DBase)))
      unlinkRedeclChain(S.getASTContext(), DBase, Prev);
  }

  /// The newest declaration of whatever D redeclares that still lives outside
  /// the DiscardedTU, or null if DiscardedTU introduced the name.
  NamedDecl *findSurvivor(NamedDecl *D) const {
    for (Decl *Prev = D->getPreviousDecl(); Prev;
         Prev = Prev->getPreviousDecl())
      if (Prev->getTranslationUnitDecl() != DiscardedTU)
        return dyn_cast<NamedDecl>(Prev);
    return nullptr;
  }

  template <typename DeclT>
  void unlinkRedeclChain(ASTContext &C, Redeclarable<DeclT> *DBase,
                         NamedDecl *PrevND) {
    auto *Latest = static_cast<DeclT *>(DBase);
    auto *Survivor = cast<DeclT>(PrevND);

    // Rebuild First -> ... -> Survivor -> ... -> Latest as
    // First -> ... -> Survivor.
    Latest->getFirstDecl()->RedeclLink.setLatest(Survivor);

    // The chain is circular: a withdrawn declaration still linked into it can
    // never walk back around to itself, so redecls() on one would not
    // terminate. Give each withdrawn declaration a chain of its own.
    for (DeclT *Dead = Latest; Dead != Survivor;) {
      DeclT *Next = Dead->getPreviousDecl();
      Dead->First = Dead;
      Dead->RedeclLink = Redeclarable<DeclT>::LatestDeclLink(C);
      Dead = Next;
    }
  }

  /// Remove entry from "C"'s lookup tables
  void removeFromLookups(NamedDecl *D) {
    if (D->getDeclName().isEmpty())
      return;

    if (D->getDeclName().isIdentifier() && D->getDeclName().getFETokenInfo() &&
        !D->getLangOpts().ObjC && !D->getLangOpts().CPlusPlus)
      S.IdResolver.RemoveDecl(D);
    // cppsh: in C++ too, one the translation unit's scope holds (a top-level
    // declaration taken back for its staging, parsed again next): out of
    // that scope and of its name's chain, which unqualified lookup at the
    // top level reads before the translation unit's own table.
    else if (D->getLangOpts().CPlusPlus && S.TUScope &&
             S.TUScope->isDeclScope(D)) {
      S.TUScope->RemoveDecl(D);
      bool OnChain = false;
      if (D->getDeclName().getFETokenInfo())
        for (auto I = S.IdResolver.begin(D->getDeclName()),
                  E = S.IdResolver.end();
             I != E && !OnChain; ++I)
          OnChain = *I == D;
      if (OnChain)
        S.IdResolver.RemoveDecl(D);
    }

    ExternCContextDecl *ECCD = S.getASTContext().getExternCContextDecl();
    if (StoredDeclsMap *Map = ECCD->getPrimaryContext()->getLookupPtr()) {
      auto It = Map->find(D->getDeclName());
      if (It != Map->end())
        It->second.remove(D);
    }
  }

  /// Remove Decls defined in this DC from the lookup table
  /// and restore the redeclaration chain to previous state
  void VisitDeclContext(DeclContext *DC) {
    llvm::SmallVector<Decl *, 8> Members(DC->noload_decls());
    llvm::SmallVector<NamedDecl *, 8> Survivors;
    for (Decl *M : Members) {
      if (M->isFromASTFile())
        continue;
      if (auto *ND = dyn_cast<NamedDecl>(M))
        if (NamedDecl *Prev = findSurvivor(ND))
          Survivors.push_back(Prev);
      Visit(M);          // restore redecls
      DC->removeDecl(M); // remove from lookup
      if (auto *ND = dyn_cast<NamedDecl>(M))
        removeFromLookups(ND);
    }

    // Restore lookup for the surviving predecessor
    // of any removed decl that had a surviving predecessor
    DeclContext *Primary = DC->getPrimaryContext();
    for (NamedDecl *Prev : Survivors)
      Primary->makeDeclVisibleInContext(Prev);
  }

public:
  ASTDeclUnmerger(Sema &S, TranslationUnitDecl *DiscardedTU)
      : S(S), DiscardedTU(DiscardedTU) {}

  void VisitDecl(Decl *D) {
    if (auto *DC = dyn_cast<DeclContext>(D))
      VisitDeclContext(DC);
  }

  void VisitFunctionDecl(FunctionDecl *D) { withdraw(D); }
  void VisitNamespaceAliasDecl(NamespaceAliasDecl *D) { withdraw(D); }
  void VisitTypedefNameDecl(TypedefNameDecl *D) { withdraw(D); }
  void VisitUsingShadowDecl(UsingShadowDecl *D) { withdraw(D); }
  void VisitVarDecl(VarDecl *D) { withdraw(D); }

  void VisitTagDecl(TagDecl *D) {
    NamedDecl *Prev = findSurvivor(D);
    if (!Prev)
      return;
    unlinkRedeclChain(S.getASTContext(), D, Prev);

    // A class definition is kept in DefinitionData outside the
    // redeclaration chain
    auto *RD = dyn_cast<CXXRecordDecl>(Prev);
    if (!RD)
      return;
    if (CXXRecordDecl *Def = RD->getDefinition();
        Def && Def->getTranslationUnitDecl() == DiscardedTU)
      for (auto *R : RD->redecls())
        cast<CXXRecordDecl>(R)->DefinitionData = nullptr;
  }

  void VisitRedeclarableTemplateDecl(RedeclarableTemplateDecl *D) {
    withdraw(D);
    Visit(D->getTemplatedDecl());
  }

  void VisitNamespaceDecl(NamespaceDecl *D) {
    // Handle cases of nested redeclarations like:
    // PTU1: namespace outer { namespace ns { class Foo; } }
    // PTU2: namespace outer { namespace ns { class Foo { ... }; error; } }
    // Foo's redeclaration needs to be restored
    VisitDeclContext(D);
    withdraw(D);
  }

  void VisitTranslationUnitDecl(TranslationUnitDecl *D) { VisitDeclContext(D); }
};

void IncrementalParser::CleanUpPTU(TranslationUnitDecl *MostRecentTU) {
  ASTDeclUnmerger(S, MostRecentTU).Visit(MostRecentTU);

  // Lookup alone is not enough: the redeclaration chain still reaches these.
  withdrawMostRecentTU(MostRecentTU);
}

PartialTranslationUnit &
IncrementalParser::RegisterPTU(TranslationUnitDecl *TU,
                               std::unique_ptr<llvm::Module> M /*={}*/) {
  PTUs.emplace_back(PartialTranslationUnit());
  PartialTranslationUnit &LastPTU = PTUs.back();
  LastPTU.TUPart = TU;

  if (!M)
    M = Act->GenModule();

  assert((!Act->getCodeGen() || M) && "Must have a llvm::Module at this point");

  LastPTU.TheModule = std::move(M);
  LLVM_DEBUG(llvm::dbgs() << "compile-ptu " << PTUs.size() - 1
                          << ": [TU=" << LastPTU.TUPart);
  if (LastPTU.TheModule)
    LLVM_DEBUG(llvm::dbgs() << ", M=" << LastPTU.TheModule.get() << " ("
                            << LastPTU.TheModule->getName() << ")");
  LLVM_DEBUG(llvm::dbgs() << "]\n");
  return LastPTU;
}
} // end namespace clang
