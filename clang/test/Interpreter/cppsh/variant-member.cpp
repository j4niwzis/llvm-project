// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A member of every alternative read through the variant.
std::sh::fs_entry e = std::sh::dir_entry{"x"}; std::println("name {}", e.name);
// CHECK: name x

// A member function of every alternative called through the variant: the
// alternative's own.
std::println("dir {}", e.is_dir());
// CHECK: dir true
