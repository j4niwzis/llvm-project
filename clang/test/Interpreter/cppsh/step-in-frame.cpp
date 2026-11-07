// RUN: printf '3\n4\n5\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A statement that needs a value read as its function runs, and declares
// nothing: compiled with the value when it runs, against the function's own
// locals -- and the function goes on in its frame, its type its own.
f() = { int n = 0; std::cin >> n; std::println("size {}", std::array<int, n>{}.size()); std::println("after {}", n); return n * 2; };
std::println("f {}", f());
// CHECK: size 3
// CHECK: after 3
// CHECK: f 6

// In a loop: a local it changes and the loop's variable, both by reference,
// the one it only reads a value it is compiled with -- each iteration
// compiled once for its value.
g() = { int total = 0; for (int i = 1; i <= 3; ++i) { total += std::array<int, i>{}.size(); } return total; };
std::println("g {}", g());
// CHECK: g 6

// One that declares what follows uses: the rest of its block compiled so --
// the loop around it the function's own, a break of it left through the
// frame.
h() = { int s = 0; for (int i = 1; i <= 5; ++i) { std::array<int, i> a{}; s += a.size(); if (i == 2) break; } return s; };
std::println("h {}", h());
// CHECK: h 3

// The rest of the body itself, where it returns nothing.
k() = { int n = 0; std::cin >> n; std::array<int, n> a{}; std::println("k {}", a.size()); };
k();
// CHECK: k 4

// A return of the function from the region: its value through the frame.
int r() { int n = 0; std::cin >> n; std::array<int, n> a{}; return static_cast<int>(a.size()) + 1; }
std::println("r {}", r());
// CHECK: r 6
