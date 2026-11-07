// RUN: printf '4\n3\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A run-time local as a template argument in a template's body -- a generic
// lambda's, a function template's: the statement staged as the body is
// parsed, compiled once its instantiation runs.
auto glam = [](auto m) { int n = 0; std::cin >> n; std::array<int, n> a; return static_cast<int>(a.size()) + m; };
std::println("g {}", glam(100));
// CHECK: g 104

template <class T> int tf(T m) { int n = 0; std::cin >> n; std::array<int, n> a; return static_cast<int>(a.size()) + m; }
std::println("t {}", tf(10));
// CHECK: t 13
