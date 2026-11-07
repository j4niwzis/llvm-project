// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// std::visit / .visit with f giving a different type for each alternative:
// the type of the call the one of the alternative held.
std::variant<int, std::string> v = 7;
auto twice = [](const auto &x) { return x + x; };
auto a = std::visit(twice, v);
std::println("a {}", a);
// CHECK: a 14
v = std::string("ab");
auto b = v.visit(twice);
std::println("b {}", b);
// CHECK: b abab
// One type for all: C++'s visit as written.
auto n = std::visit([](const auto &x) { return sizeof(x) > 0; }, v);
std::println("n {}", n);
// CHECK: n true
