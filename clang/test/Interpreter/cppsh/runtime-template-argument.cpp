// RUN: printf '4\n6\n2\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A default template argument read at run time -- plain C++, every kind of
// template: evaluated once where it is used, the rest compiled with it.
int input_int() { int v = 0; std::cin >> v; return v; }

template <auto N = input_int()> auto f() { return N; }
std::println("function {}", f());
// CHECK: function 4

template <int N = input_int()> struct box { static constexpr int size = N; };
show_box() = { box<> b; return b.size; };
std::println("class {}", show_box());
// CHECK: class 6

g() = { std::array<int, input_int()> a{}; return a.size(); };
std::println("array {}", g());
// CHECK: array 2
