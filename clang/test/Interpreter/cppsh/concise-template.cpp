// RUN: printf '41\n3\n7\n5\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

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

// Template parameters named, no parameters at all.
g<T> = { T response; std::cin >> response; ^ response; }
std::println("got {}", g<int>());
// CHECK: got 7

// A value template parameter whose default is read at run time: foo() reads
// it and calls foo<it>; foo<9>() the template itself.
foo<obj: int = input<int>()> = obj;
std::println("foo {} {}", foo(), foo<9>());
// CHECK: foo 5 9
