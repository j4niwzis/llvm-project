// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A member function template specialized on its arguments' values as a free
// one is: each value its own specialization, its own symbol.
struct opts { bool whole; };
struct picker {
  template <class T> auto pick(const T &o) const { if (o.whole) return 1; else return 2.5; }
};
constexpr picker pk{};
constexpr opts c{true};
std::println("m {}", pk.pick(c));
// CHECK: m 1
std::println("n {}", pk.pick(opts{false}));
// CHECK: n 2.5
