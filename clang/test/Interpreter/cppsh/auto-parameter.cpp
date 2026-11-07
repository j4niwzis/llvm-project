// RUN: rm -rf %t && mkdir -p %t/d/sub && touch %t/d/a.txt
// RUN: cd %t/d && printf '1\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A function with an auto parameter, cut while its body is instantiated; a C
// string handed to the continuation rebuilt as a literal.
h dir: T' = { o = ls_opts{}; std::cin >> o.files_only; return ls dir o; }; h(".") | show

// CHECK: name
// CHECK-NOT: type
// CHECK: a.txt
