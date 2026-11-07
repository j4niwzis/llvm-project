// RUN: printf '2.5\n3 4\n5\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// Run-time template arguments of types other than integers: evaluated once
// where they are used, the rest compiled with their values.
double input_double() { double v = 0; std::cin >> v; return v; }
template <double D> auto half() { return D / 2; }
g() = { return half<input_double()>(); };
std::println("half {}", g());
// CHECK: half 1.25

// A class type (structural): its value read whole.
struct point { int x, y; };
point input_point() { point p{}; std::cin >> p.x >> p.y; return p; }
template <point P> int sum() { return P.x + P.y; }
h() = { return sum<input_point()>(); };
std::println("sum {}", h());
// CHECK: sum 7

// At the top level: the statement compiled again with the value.
std::println("top {}", half<input_double()>());
// CHECK: top 2.5
