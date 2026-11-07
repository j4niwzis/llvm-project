// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A script runs a line at a time: a line with no ; does not run on into the
// next one, and an error in one input does not take the next with it.
std::println("one")
std::println("two");
// CHECK: one
// CHECK: two
