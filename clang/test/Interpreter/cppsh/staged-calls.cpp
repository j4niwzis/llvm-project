// RUN: printf '3\n4\n5\n6\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// Several staged calls in one statement: each staged function's result (of
// a type known once it ran) a parameter of its own, in the order the calls
// are made.
g() = { n = 0; std::cin >> n; return std::array<int, n>{}; };
t() = { return g().size() * 10 + g().size(); };
std::println("t {}", t());
// CHECK: t 34

// At the top level.
std::println("u {}", g().size() * 10 + g().size());
// CHECK: u 56
