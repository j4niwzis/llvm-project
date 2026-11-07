// RUN: printf '3\n5\n4\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

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

// A co_return of staged code: the coroutine it is in ends there (its
// promise's return_void).
gen early() { int n = 0; std::cin >> n; std::array<int, n> a{}; for (std::size_t i = 0; i < a.size(); ++i) { if (i == 2) co_return; co_yield static_cast<int>(i); } }
{ auto g = early(); while (g.next()) std::println("e {}", g.value()); std::println("early done"); }
// CHECK: e 0
// CHECK-NEXT: e 1
// CHECK-NEXT: early done

// A co_await of staged code: the coroutine it is in suspended with the
// awaiter, resumed through the staged code.
gen waits() { int n = 0; std::cin >> n; std::array<int, n> a{}; co_await std::suspend_always{}; co_yield static_cast<int>(a.size()); }
{ auto g = waits(); int k = 0; while (g.next()) { ++k; std::println("w {} {}", k, g.value()); } }
// CHECK: w 1 0
// CHECK-NEXT: w 2 4
