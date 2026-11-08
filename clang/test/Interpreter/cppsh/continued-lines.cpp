// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// A line beginning with an operator that takes a left operand goes on with
// the statement before it: a pipeline, a call chain, a stream, over lines.
auto r = std::views::iota(1, 4)
  | std::views::transform([](int x) { return x * 2; });
for (int x : r) std::print("{} ", x);
std::println("");
// CHECK: 2 4 6
std::string s = std::string("xy")
  // a comment between
  .append("z");
std::println("{}", s);
// CHECK: xyz
std::cout << "a"
  << "b" << std::endl;
// CHECK: ab
