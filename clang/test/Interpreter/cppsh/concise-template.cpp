// RUN: printf '41\n3\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A concise function of explicit template parameters, a parameter with a
// default without parentheses, ^ for return.
input<T> text: std::string_view = {} = { T response; std::cin >> response; ^ response; }
std::println("read {}", input<int>("number? ") + 1);
// CHECK: read 42

// A default read at run time as a template argument: each call cut, its
// array of the size read.
f3 (x: int = input<int>("")) = std::array<int, x>{};
std::println("size {}", f3().size());
// CHECK: size 3
