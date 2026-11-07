//===--- CppshStaging.h - cppsh's staged functions --------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// What the cut of a staged function hands over (cppsh): shared by the parser
// and Sema, which make cuts, and the interpreter, which runs their
// continuations (__cppsh_cut_run).
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_SEMA_CPPSHSTAGING_H
#define LLVM_CLANG_SEMA_CPPSHSTAGING_H

#include "clang/AST/Type.h"
#include "clang/Lex/Token.h"
#include <optional>
#include <vector>

namespace clang {
class IdentifierInfo;
class SourceManager;

/// One entry of a cut's frame: a live local, or the value of a run-time
/// template argument (a long long, Name null).
struct CppshCutLocal {
  const IdentifierInfo *Name = nullptr;
  /// Its type, unqualified, not a reference.
  QualType Type;
  /// Handed over by moving it: a type with no copy.
  bool Move = false;
  /// Taken by reference, not as a value it is compiled with: a local the
  /// code changes, or that has no copy (a step's: CppshStep).
  bool ByRef = false;
};

/// Per cut, its frame, in order.
extern std::vector<std::vector<CppshCutLocal>> CppshCutLocals;

/// Every token of what the user typed (the REPL's input buffers), as the
/// preprocessor gave it, each once and in order -- what code compiled later
/// is parsed from, never its text again. Recorded by the preprocessor's
/// token watcher (IncrementalParser).
extern std::vector<Token> CppshInputTokens;
void cppshRecordToken(const SourceManager &SM, const Token &T);
/// Where the token at Loc is in CppshInputTokens; none where it is not one.
std::optional<unsigned> cppshTokenIndex(SourceLocation Loc);

/// A statement run on its own when its function runs (Parser::
/// CppshEmitStep): its tokens [Begin, End) of CppshInputTokens, its frame,
/// and whether the function running it is built (__cppsh_step_run).
struct CppshStep {
  unsigned Begin = 0, End = 0;
  std::vector<CppshCutLocal> Frame;
  bool Built = false;
};
extern std::vector<CppshStep> CppshSteps;
} // namespace clang

#endif // LLVM_CLANG_SEMA_CPPSHSTAGING_H
