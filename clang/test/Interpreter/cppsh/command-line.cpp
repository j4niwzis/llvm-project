// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A line beginning with `$`: the rest of it run by the system shell, as it
// is written -- its pipes, arithmetic and quoting the shell's.
$echo "from the shell: $((1+2))" | tr a-z A-Z
// CHECK: FROM THE SHELL: 3
$ printf '%s\n' "spaced too"
// CHECK: spaced too
std::println("status {}", std::sh::last_status);
// CHECK: status 0
