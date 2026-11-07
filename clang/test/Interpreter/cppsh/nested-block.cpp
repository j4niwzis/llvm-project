// RUN: rm -rf %t && mkdir -p %t/d/sub && touch %t/d/a.txt
// RUN: cd %t/d && printf '1 1\n' | cppsh %s 2>&1 | FileCheck %s --check-prefix=TAKEN --implicit-check-not=error: --implicit-check-not=warning:
// RUN: cd %t/d && printf '0\n' | cppsh %s 2>&1 | FileCheck %s --check-prefix=NOT --implicit-check-not=error: --implicit-check-not=warning:

// A need inside a nested block, of a local declared there: cut in the block;
// the block around it cuts after it too, so every way out is staged alike.
g() = { c = 0; std::cin >> c; if (c) { o = ls_opts{}; std::cin >> o.files_only; return ls o; } return ls; }; g() | show

// TAKEN: name
// TAKEN-NOT: type
// TAKEN: a.txt

// NOT: type
// NOT-DAG: a.txt{{.*}}file
// NOT-DAG: sub{{.*}}dir
