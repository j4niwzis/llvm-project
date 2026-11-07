// A benchmark of staged code (not a test): run it as
//   cppsh clang/tools/cppsh/bench/staged-values.cpp
// What it measures, in milliseconds:
//   same:  one staged statement reached 100000 times with the same value --
//          the cost of reaching compiled staged code (prepare, the call, done);
//   many:  one staged statement reached with 50 different values -- the cost
//          of compiling it for each new one;
//   plain: the same loop as `same` with no staged code, for comparison.

int same(int k) { int n = 4; std::array<int, n> a{}; return static_cast<int>(a.size()) + k; }
int plain(int k) { std::array<int, 4> a{}; return static_cast<int>(a.size()) + k; }
int many(int n) { std::array<int, n> a{}; return static_cast<int>(a.size()); }

template <class F> double ms(F f) {
  auto t0 = std::chrono::steady_clock::now();
  f();
  return std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count();
}

{ long t = 0; same(0); double d = ms([&] { for (int i = 0; i < 100000; ++i) t += same(i); }); std::println("same  {:8.1f} ms ({:.2f} us each) {}", d, d * 10, t); }
{ long t = 0; double d = ms([&] { for (int i = 0; i < 100000; ++i) t += plain(i); }); std::println("plain {:8.1f} ms ({:.4f} us each) {}", d, d * 10, t); }
{ long t = 0; double d = ms([&] { for (int i = 1; i <= 50; ++i) t += many(i); }); std::println("many  {:8.1f} ms ({:.1f} ms each) {}", d, d / 50, t); }
