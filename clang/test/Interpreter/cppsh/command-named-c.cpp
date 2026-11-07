// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// sleep is the program, not <unistd.h>'s function; that one stays ::sleep.
std::println("program {}", (sleep 0).status());
// CHECK: program 0
std::println("c function {}", ::sleep(0));
// CHECK: c function 0
