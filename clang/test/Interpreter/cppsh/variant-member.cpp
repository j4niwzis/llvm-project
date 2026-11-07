// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A member of every alternative read through the variant.
std::sh::fs_entry e = std::sh::dir_entry{"x"}; std::println("name {}", e.name);
// CHECK: name x
