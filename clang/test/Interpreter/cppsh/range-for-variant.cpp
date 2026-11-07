// RUN: rm -rf %t && mkdir -p %t/d/sub && touch %t/d/a.txt
// RUN: cd %t/d && printf '0\n' | cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A need in a range-for header: cut at the whole loop. e.name on a variant
// entry: the member of the alternative it holds. c, changed in the loop, is
// not specialized on its value.
w() = { o = ls_opts{}; std::cin >> o.files_only; c = 0; for (e : ls o) { ++c; std::println("entry {}", e.name); } return c; }; w()

// CHECK-DAG: entry a.txt
// CHECK-DAG: entry sub
// CHECK: (int) 2
