// RUN: rm -rf %t && mkdir -p %t/d/sub && touch %t/d/a.txt
// RUN: cd %t/d && printf '1\n' | cppsh %s 2>&1 | FileCheck %s --check-prefix=FILES --implicit-check-not=error: --implicit-check-not=warning:
// RUN: cd %t/d && printf '0\n' | cppsh %s 2>&1 | FileCheck %s --check-prefix=ALL --implicit-check-not=error: --implicit-check-not=warning:

// A value read at run time (std::cin) decides, at compile time, what ls
// returns -- inside a function, in one input: the function is cut at the
// need, the rest compiled once the value is known.
f() = { o = ls_opts{}; std::cin >> o.files_only; return ls o; }; x = f(); x | show

// files_only: a range of file_entry -- no kind column, no directory.
// FILES: name
// FILES-NOT: type
// FILES: a.txt
// FILES-NOT: sub

// Every kind: the variant range, its kind column.
// ALL: type
// ALL-DAG: a.txt{{.*}}file
// ALL-DAG: sub{{.*}}dir
