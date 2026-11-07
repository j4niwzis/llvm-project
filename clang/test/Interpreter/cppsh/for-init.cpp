// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// for (i = 0; ...): the implicit auto declaration in a for-init too.
p() = { s = 0; for (i = 0; i < 4; ++i) s += i; return s; }; p()
// CHECK: (int) 6
