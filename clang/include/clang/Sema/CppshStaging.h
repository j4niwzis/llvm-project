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
class FunctionDecl;
class Expr;
class Sema;
class VarDecl;
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
  /// code changes, or that has no copy.
  bool ByRef = false;
};


/// Every token of what the user typed (the REPL's input buffers), as the
/// preprocessor gave it, each once and in order -- what code compiled later
/// is parsed from, never its text again. Recorded by the preprocessor's
/// token watcher (IncrementalParser).
extern std::vector<Token> CppshInputTokens;
void cppshRecordToken(const SourceManager &SM, const Token &T);
/// Where the token at Loc is in CppshInputTokens; none where it is not one.
std::optional<unsigned> cppshTokenIndex(SourceLocation Loc);

/// Whether a function is a staged region's call operator (Parser::
/// CppshEmitRegion): code whose types may depend on values that exist only as
/// its function runs, a need met in it a region of its own.
bool cppshIsRegion(const FunctionDecl *FD);

/// In a template's body the user wrote, the local a value-dependent template
/// argument names -- not a parameter, not a constant: a value that exists
/// only as the function runs, whatever the template is instantiated with
/// (a need, met as the body is parsed). None elsewhere: Sema meets those
/// as the argument is checked.
const VarDecl *cppshTemplateLocalIn(Sema &S, const Expr *E);

/// Whether what is being parsed is in a top-level statement (the REPL's),
/// outside any function: a need met there makes a staged region too.
bool cppshInTopStatement(Sema &S);
} // namespace clang

#endif // LLVM_CLANG_SEMA_CPPSHSTAGING_H
