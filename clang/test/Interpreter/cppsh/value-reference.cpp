// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A parameter taken by reference to const, specialized on its argument's
// value as one taken by value is: the `if` on it folded, each branch's
// return its own type.
struct opts { bool whole; };
template <class T> auto pick(const T &o) { if (o.whole) return 1; else return 2.5; }
constexpr opts c{true};
std::println("p {}", pick(c));
// CHECK: p 1
std::println("q {}", pick(opts{false}));
// CHECK: q 2.5
