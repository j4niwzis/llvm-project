// RUN: rm -rf %t && mkdir -p %t/bin %t/d/sub && touch %t/d/sub/notes.txt
// RUN: printf '#!/bin/sh\necho "ran: $*"\n' > %t/bin/my-tool && chmod +x %t/bin/my-tool
// RUN: cd %t/d && env PATH=%t/bin:/usr/bin:/bin cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error:

// kebab-case: a '-' between two parts of a name is one name -- a command's
// (my-tool) or an argument's (some-thing); paths and files one word each.
my-tool -v sub/notes.txt some-thing
// CHECK: ran: -v sub/notes.txt some-thing

// A name of the user's own, in kebab-case.
item-count = 3; std::println("item-count is {}", item-count);
// CHECK: item-count is 3

// Not before a digit, nor with spaces: a subtraction.
n = 5; m = 2; std::println("{} {}", n-1, n - m);
// CHECK: 4 3
