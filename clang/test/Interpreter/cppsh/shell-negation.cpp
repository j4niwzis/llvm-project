// RUN: rm -rf %t && mkdir -p %t/d/sub && touch %t/d/a.txt
// RUN: cd %t/d && cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A negation as a command's word: `filter !_.is_dir()`, the predicate negated
// (no binary `!` it could be read as instead) -- is_dir a member function of
// each kind of entry, called on the one the variant holds.
ls | filter !_.is_dir() | show
// CHECK: a.txt
// CHECK-NOT: sub
