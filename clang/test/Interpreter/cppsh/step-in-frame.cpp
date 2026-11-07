// RUN: printf '3\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A statement that needs a value read as its function runs, and declares
// nothing: compiled with the value when it runs, against the function's own
// locals -- and the function goes on in its frame, its type its own.
f() = { int n = 0; std::cin >> n; std::println("size {}", std::array<int, n>{}.size()); std::println("after {}", n); return n * 2; };
std::println("f {}", f());
// CHECK: size 3
// CHECK: after 3
// CHECK: f 6

// In a loop: a local it changes taken by reference, the loop's variable by
// value -- each iteration compiled once for its value.
g() = { int total = 0; for (int i = 1; i <= 3; ++i) { total += std::array<int, i>{}.size(); } return total; };
std::println("g {}", g());
// CHECK: g 6
