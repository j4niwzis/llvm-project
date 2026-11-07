// RUN: printf '3\n2\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// An exception thrown by staged code: through the code compiled for it,
// into the function around it, and on to whoever catches it.
int thrower() { int n = 0; std::cin >> n; std::array<int, n> a{}; if (a.size() == 3) throw std::runtime_error("three"); return static_cast<int>(a.size()); }
try { std::println("t {}", thrower()); } catch (const std::exception &e) { std::println("caught {}", e.what()); }
// CHECK: caught three

// Caught in the function itself, by a handler around the staged code.
int inner() { int n = 0; std::cin >> n; try { std::array<int, n> a{}; if (a.size() == 2) throw 7; return 1; } catch (int v) { return v * 10; } }
std::println("i {}", inner());
// CHECK: i 70

// The interpreter is left as it was: staged code runs on after it.
int after() { int n = 3; std::array<int, n> a{}; return static_cast<int>(a.size()); }
std::println("a {}", after());
// CHECK: a 3
