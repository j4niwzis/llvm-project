// RUN: rm -rf %t && mkdir -p %t/bin %t/d/sub && touch %t/d/sub/notes.txt
// RUN: printf '#!/bin/sh\necho "ran: $*"\n' > %t/bin/my-tool && chmod +x %t/bin/my-tool
// RUN: cd %t/d && env PATH=%t/bin:/usr/bin:/bin cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// A command named with a '-' in it, and arguments with '/', '.' and '-':
// one word each, where their first part names nothing C++ knows.
my-tool -v sub/notes.txt some-thing
// CHECK: ran: -v sub/notes.txt some-thing

// A name C++ knows keeps its meaning.
n = 5; std::println("n-1 is {}", n-1);
// CHECK: n-1 is 4
