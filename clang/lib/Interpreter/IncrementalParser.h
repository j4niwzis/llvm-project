//===--- IncrementalParser.h - Incremental Compilation ----------*- C++ -*-===//
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

#ifndef LLVM_CLANG_LIB_INTERPRETER_INCREMENTALPARSER_H
#define LLVM_CLANG_LIB_INTERPRETER_INCREMENTALPARSER_H

#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Error.h"

#include "clang/Sema/Sema.h"

#include <list>
#include <optional>
#include <memory>

namespace clang {
class ASTConsumer;
class CompilerInstance;
class Parser;
class Sema;
class TranslationUnitDecl;
class IncrementalAction;
struct PartialTranslationUnit;

/// Provides support for incremental compilation. Keeps track of the state
/// changes between the subsequent incremental input.
///
class IncrementalParser {
protected:
  /// The Sema performing the incremental compilation.
  Sema &S;

  /// Parser.
  std::unique_ptr<Parser> P;

  /// Consumer to process the produced top level decls. Owned by Act.
  ASTConsumer *Consumer = nullptr;

  /// Counts the number of direct user input lines that have been parsed.
  unsigned InputCount = 0;

  /// The FrontendAction used during incremental parsing.
  IncrementalAction *Act = nullptr;

  std::list<PartialTranslationUnit> &PTUs;

public:
  IncrementalParser(CompilerInstance &Instance, IncrementalAction *Act,
                    llvm::Error &Err, std::list<PartialTranslationUnit> &PTUs);
  virtual ~IncrementalParser();

  /// Parses incremental input by creating an in-memory file.
  ///\returns a \c PartialTranslationUnit which holds information about the
  /// \c TranslationUnitDecl.
  virtual llvm::Expected<TranslationUnitDecl *> Parse(llvm::StringRef Input);

  void CleanUpPTU(TranslationUnitDecl *MostRecentTU);

  /// cppsh: the parser, for code built from recorded tokens.
  Parser &getParser() { return *P; }

  /// cppsh: an input parsed one top-level declaration at a time, each a unit
  /// of its own -- begun, then each in turn (Done once there is none left);
  /// the rest of it skipped where one failed.
  llvm::Error BeginInput(llvm::StringRef Input);
  llvm::Expected<TranslationUnitDecl *> ParseNextTopLevel(bool First, bool &Done);
  void SkipInput();

  /// cppsh: a unit built by Sema rather than parsed -- begun, each
  /// declaration of it handed over, then finished as a parsed one is.
  llvm::Error BeginBuild();
  void AddBuilt(DeclGroupRef DG);
  llvm::Expected<TranslationUnitDecl *> EndBuild();

  /// Register a PTU produced by Parse.
  PartialTranslationUnit &RegisterPTU(TranslationUnitDecl *TU,
                                      std::unique_ptr<llvm::Module> M = {});

private:
  llvm::Expected<TranslationUnitDecl *> ParseOrWrapTopLevelDecl();

  /// A new unit, the scope of the last one left.
  void StartPTU();
  /// The unit taken back whole (it failed): why, as the error.
  llvm::Error TakeBackPTU(llvm::StringRef Why);
  /// The unit finished: its instantiations performed, code generated.
  llvm::Expected<TranslationUnitDecl *>
  FinishPTU(Sema::LocalEagerInstantiationScope &LocalInstantiations,
            Sema::GlobalEagerInstantiationScope &GlobalInstantiations);

  /// The consumer rejected a declaration of the unit being built.
  bool ConsumerFailed = false;
  // cppsh: how many of Sema's UndefinedButUsed there were as the unit began.
  size_t UndefinedUsedAtStart = 0;
  /// Parsing an input one top-level declaration at a time, past its first.
  bool StepwiseInput = false;
  /// The instantiation scopes of the unit being built.
  std::optional<Sema::GlobalEagerInstantiationScope> BuildGlobalInstantiations;
  std::optional<Sema::LocalEagerInstantiationScope> BuildLocalInstantiations;

  /// Rebuild the translation unit redeclaration chain without \p MostRecentTU,
  /// making its predecessor the current unit again.
  void withdrawMostRecentTU(TranslationUnitDecl *MostRecentTU);
};
} // end namespace clang

#endif // LLVM_CLANG_LIB_INTERPRETER_INCREMENTALPARSER_H
