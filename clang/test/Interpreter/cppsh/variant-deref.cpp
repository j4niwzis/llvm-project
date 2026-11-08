// RUN: cppsh %s 2>&1 | FileCheck %s --implicit-check-not=error: --implicit-check-not=warning:

// *v on a std::variant: the value it holds, of the type it holds -- known
// once the index is, as the statement runs.
int obj = *std::variant<int, std::string>{42};
std::println("obj {}", obj);
// CHECK: obj 42
std::variant<int, std::string> v = std::string("hi");
std::string s = *v;
std::println("s {}", s);
// CHECK: s hi
auto print_held(std::variant<int, double> x) {
  auto y = *x;
  std::println("{}", y);
}
print_held(3);
// CHECK: 3
print_held(1.5);
// CHECK: 1.5
// A loop's variable: its index read each time round, the type of what it
// holds each time its own.
for (auto e : std::vector<std::variant<int, std::string>>{1, std::string("a")}) {
  auto item = *e;
  std::println("item {}", item);
}
// CHECK: item 1
// CHECK: item a
// v->m: (*v).m, the member of the alternative held.
struct pt { int x; };
struct named { std::string x; };
std::variant<pt, named> pv = named{"nm"};
std::println("arrow {}", pv->x);
// CHECK: arrow nm
pv = pt{5};
std::println("arrow {}", pv->x);
// CHECK: arrow 5
