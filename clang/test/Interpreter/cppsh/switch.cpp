// RUN: rm -rf %t && mkdir -p %t/d/sub && touch %t/d/a.txt
// RUN: cd %t/d && printf '1\n' | cppsh %s 2>&1 | FileCheck %s --check-prefix=CASE --implicit-check-not=error:
// RUN: cd %t/d && printf '2\n' | cppsh %s 2>&1 | FileCheck %s --check-prefix=DEFAULT --implicit-check-not=error:

// A cut in a switch: the rest of the case in do { } while (false), its labels
// dropped; what follows the switch not appended after a rest that returns.
sw() = { k = 0; std::cin >> k; switch (k) { case 1: { o = ls_opts{}; o.files_only = true; return ls o; } default: break; } return ls; }; sw() | show

// CASE: name
// CASE-NOT: type
// CASE: a.txt

// DEFAULT: type
