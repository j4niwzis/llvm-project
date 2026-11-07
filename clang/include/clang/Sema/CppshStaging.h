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
#include "llvm/ADT/DenseMap.h"
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

/// In a template's body the user wrote, the local a value-dependent template
/// argument names -- not a parameter, not a constant: a value that exists
/// only as the function runs, whatever the template is instantiated with
/// (a need, met as the body is parsed). None elsewhere: Sema meets those
/// as the argument is checked.
const VarDecl *cppshTemplateLocalIn(Sema &S, const Expr *E);

/// What supplies an expression written (or a default substituted) at a
/// location: in a staged region, a run-time template argument or a staged
/// call of its first statement -- the region's parameter for it; in a
/// top-level declaration parsed again, a staged call's result, a run-time
/// template argument's value (Interpreter::cppshStageDecl).
extern llvm::DenseMap<SourceLocation::UIntTy, Expr *> CppshSuppliedExprs;

/// Whether staging is traced (CPPSH_TRACE_STAGING set): what is staged, why
/// not, and how each staged statement ran -- on stderr, "cppsh-trace: ".
bool cppshTraceStaging();

/// A need met in the statement being parsed (CppshCutNeeded): what the rest
/// of that statement's analysis says is held back -- it is parsed again,
/// as a staged region's -- until cppshEndNeedDiagnostics, where the
/// statement ends.
void cppshMeetNeed(Sema &S);
/// Diagnostics held back as above, without a need (a top-level
/// declaration taken back to be parsed again).
void cppshHoldDiagnostics(Sema &S);
void cppshEndNeedDiagnostics(Sema &S);

/// Whether what is being parsed is in a top-level statement (the REPL's),
/// outside any function: a need met there makes a staged region too.
bool cppshInTopStatement(Sema &S);
// The specializations on argument values made from here on: forgotten --
// not found again -- if what made them failed (a quiet attempt of staged
// code's): a body made without a value it needed may have failed short of
// marking its function invalid.
size_t cppshSpecializationMark();
void cppshForgetSpecializationsSince(size_t Mark);
// And those made in a unit taken out of the JIT (staged code's, evicted).
void cppshForgetSpecializationsIn(const TranslationUnitDecl *TU);
} // namespace clang

#endif // LLVM_CLANG_SEMA_CPPSHSTAGING_H
