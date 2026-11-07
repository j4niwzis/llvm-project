// RUN: printf '3\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// Staged code that yields from the coroutine it is in: compiled as a
// coroutine of its own, its co_yield the outer generator's.
struct gen {
  struct promise_type {
    int value = 0;
    gen get_return_object() { return gen{std::coroutine_handle<promise_type>::from_promise(*this)}; }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    std::suspend_always yield_value(int v) noexcept { value = v; return {}; }
    void return_void() noexcept {}
    void unhandled_exception() { std::terminate(); }
  };
  std::coroutine_handle<promise_type> h;
  bool next() { h.resume(); return !h.done(); }
  int value() const { return h.promise().value; }
};
gen sizes() { int n = 0; std::cin >> n; std::array<int, n> a{}; for (std::size_t i = 0; i < a.size(); ++i) co_yield static_cast<int>(i * 10); }
{ auto g = sizes(); while (g.next()) std::println("y {}", g.value()); }
// CHECK: y 0
// CHECK: y 10
// CHECK: y 20
