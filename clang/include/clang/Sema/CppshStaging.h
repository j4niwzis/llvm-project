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
#include <vector>

namespace clang {
class IdentifierInfo;

/// One entry of a cut's frame: a live local, or the value of a run-time
/// template argument (a long long, Name null).
struct CppshCutLocal {
  const IdentifierInfo *Name = nullptr;
  /// Its type, unqualified, not a reference.
  QualType Type;
  /// Handed over by moving it: a type with no copy.
  bool Move = false;
};

/// Per cut, its frame, in order.
extern std::vector<std::vector<CppshCutLocal>> CppshCutLocals;
} // namespace clang

#endif // LLVM_CLANG_SEMA_CPPSHSTAGING_H
