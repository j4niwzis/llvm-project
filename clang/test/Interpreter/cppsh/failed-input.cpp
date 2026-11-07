// RUN: cppsh %s 2>&1 | FileCheck %s

// A failed input is taken back whole -- code generation included: what it
// had code generation emit (std::string's inline functions, instantiated
// for it) is emitted again where a later input uses it, not left an
// undefined symbol (JIT session error: Symbols not found).
std::string a = "first"; std::vector<char *> v; v.emplace_back(a.data()); int broken = undeclared_name;
// CHECK: error: use of undeclared identifier 'undeclared_name'
std::string b = "second"; std::vector<char *> w; w.emplace_back(b.data()); std::println("after {}", w.size());
// CHECK-NOT: Symbols not found
// CHECK: after 1

// The same name defined again after a failure: not a second definition.
int twice() { return 1; } int also_broken = undeclared_again;
// CHECK: error: use of undeclared identifier 'undeclared_again'
int twice() { return 2; } std::println("twice {}", twice());
// CHECK-NOT: same mangled name
// CHECK: twice 2
