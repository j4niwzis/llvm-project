// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// Ordinary C++ expressions are C++, not commands with words: the shell's
// call without parentheses (`ls -l`, `ls *.cpp`) never takes a value, a
// variable, a call's result or a member access followed by an operator.
int a = 7, b = 2; int *p = &a; double x = 9, y = 3;
std::println("{} {} {} {} {} {}", a - b, a * b, x / y, *p, a % b, -a);
// CHECK: 5 14 3 7 1 -7
f() = { n = 10; m = 4; return n - m * 2 + n / m; };
std::println("f {}", f());
// CHECK: f 4
struct S { int v; int get() const { return v; } };
S s{5}; S *ps = &s;
std::println("s {} {}", ps->get() * 2, s.get() - 1);
// CHECK: s 10 4
template <class T> T mix(T v) { return v * 2 - v / 2; }
std::println("t {}", mix(8));
// CHECK: t 12
