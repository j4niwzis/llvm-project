// RUN: printf '2\n3\n0\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A value read at run time as a template argument, in a loop at the top
// level: the loop the body of a function of its own, cut at the need, each
// iteration compiled with its value -- an array of its own size.
while (true) { n = 0; std::cin >> n; if (n == 0) break; a = std::array<int, n>{}; std::println("size {}", a.size()); }
// CHECK: size 2
// CHECK: size 3
