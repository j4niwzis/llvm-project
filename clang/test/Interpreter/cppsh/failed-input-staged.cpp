// RUN: printf '6\n7\n' | not cppsh %s 2>&1 | FileCheck %s

// An input that ran staged code and then failed is taken back whole: the
// function it defined, and the code compiled for its staged statement, are
// gone -- defined again, the function is compiled again and runs.
int st() { int n = 0; std::cin >> n; std::array<int, n> a; return static_cast<int>(a.size()); } std::println("st {}", st()); int bad = undeclared_here;
// CHECK: st 6
// CHECK: int bad = undeclared_here;
int st() { int n = 0; std::cin >> n; std::array<int, n> a; return static_cast<int>(a.size()) * 10; } std::println("st {}", st());
// CHECK-NOT: same mangled name
// CHECK-NOT: Symbols not found
// CHECK: st 70
