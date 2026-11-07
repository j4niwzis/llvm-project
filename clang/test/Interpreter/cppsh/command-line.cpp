// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A line beginning with `$`: the rest of it run by the system shell, as it
// is written -- its pipes, arithmetic and quoting the shell's.
$echo "from the shell: $((1+2))" | tr a-z A-Z
// CHECK: FROM THE SHELL: 3
$ printf '%s\n' "spaced too"
// CHECK: spaced too
std::println("status {}", std::sh::last_status);
// CHECK: status 0

// `$( )` inside C++: a shell command as an expression -- captured into a
// string, piped as any command is.
std::string got = $(echo captured | tr a-z A-Z); std::println("got {}", got);
// CHECK: got CAPTURED
for (l : $(printf 'a\nb\n')) std::println("line {}", l.text);
// CHECK: line a
// CHECK: line b
