// RUN: printf '1\n0\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A function returning a different type for each value of its parameter:
// each value its own specialization, the `if` reading it folded.
f flag = {if(flag) ^ 42; else ^ "hello world"; }
std::println("{}", f(true));
// CHECK: 42
std::println("{}", f(false));
// CHECK: hello world
for (int i = 0; i < 2; ++i) { bool b = false; std::cin >> b; std::println("{}", f(b)); }
// CHECK: 42
// CHECK: hello world
