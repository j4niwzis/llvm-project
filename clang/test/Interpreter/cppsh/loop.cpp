// RUN: rm -rf %t && mkdir -p %t/d/sub && touch %t/d/a.txt
// RUN: cd %t/d && printf '1\n0\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A need in a loop body: each iteration finished with its own value, the
// loop run on by a plain function; one type per iteration. n changed in the
// continuation (++n) is not taken as a constant.
k() = { n = 0; for (i = 0; i < 2; ++i) { o = ls_opts{}; std::cin >> o.files_only; ls o | show; ++n; } return n; }; k()

// CHECK: name
// CHECK-NOT: type
// CHECK: a.txt
// CHECK: type
// CHECK: (int) 2
