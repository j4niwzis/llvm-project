// RUN: printf '3\n2\n5\n2\n2\n3\n4\n4\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A goto out of staged code, to a label of its function before it: the
// function jumps there.
int gb() { int tries = 0; int n = 0; retry: std::cin >> n; ++tries; if (tries == 1) { std::array<int, n> a; if (a.size() == 3) goto retry; } return tries * 100 + n; }
std::println("gb {}", gb());
// CHECK: gb 202

// Case labels of a switch around staged code, inside it: the code entered
// at the one the switch jumps to.
int sw(int k) { int n = 0; std::cin >> n; switch (k) { case 0: std::array<int, n> a; return static_cast<int>(a.size()); case 1: return n * 10; } return -1; }
std::println("sw0 {}", sw(0));
// CHECK: sw0 5
std::println("sw1 {}", sw(1));
// CHECK: sw1 20

// Staged code inside staged code, returning from the function both are in.
int nr() { int n = 0; std::cin >> n; std::array<int, n> a; for (int i = 0; i < 3; ++i) { std::array<int, i + 1> b; if (b.size() == 2) return static_cast<int>(a.size() * 10 + b.size()); } return -1; }
std::println("nr {}", nr());
// CHECK: nr 22

// A static local of staged code: one object, whatever the code is compiled
// for each time.
int counter() { int n = 0; std::cin >> n; std::array<int, n> a; static int calls = 0; ++calls; return calls * 10 + static_cast<int>(a.size()); }
std::println("c1 {}", counter());
// CHECK: c1 13
std::println("c2 {}", counter());
// CHECK: c2 24

// Staged code in a lambda's body.
auto lam = [](int m) { int n = 0; std::cin >> n; std::array<int, n> a; return static_cast<int>(a.size()) + m; };
std::println("lam {}", lam(100));
// CHECK: lam 104
