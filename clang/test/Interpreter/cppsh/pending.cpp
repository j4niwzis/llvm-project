// RUN: printf '5\n7\n' | env CPPSH_TRACE_STAGING=1 cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A run-time local handed to a function that may be specialized on its
// arguments' values, but whose instantiation never reads it: nothing staged,
// the value passed as the function runs.
template <class T> auto twice(T v) { return v * 2; }
int f() { int n = 0; std::cin >> n; return twice(n); }
std::println("f {}", f());
// CHECK-NOT: cppsh-trace: staged at
// CHECK: f 10

// One whose instantiation reads it as a constant: the code from there staged,
// compiled for the value it has.
template <class T> auto count(T v) { return std::array<int, v>{}.size(); }
int g() { int n = 0; std::cin >> n; return static_cast<int>(count(n)); }
std::println("g {}", g());
// CHECK: cppsh-trace: staged at
// CHECK: g 7
