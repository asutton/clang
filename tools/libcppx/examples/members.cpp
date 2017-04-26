#include <iostream>

#include <cppx/meta>

struct S {
  S(const S&) { }
  S(S&&) { }

  void member_f1() { }
  void member_f2() { }

  static void static_f1() { }
  static void static_f2() { }

  int member_v1;
  int member_v2;

  static int static_v1;
  static int static_v2;

public:
  int x;
private:
  int y;
protected:
  int z;
};

int main() {
  // All members
  std::cout << "all members:\n";
  for... (auto x : $S.members())
    std::cout << "member: " << x.qualified_name()
              << " : " << $x.type().name() << '\n';
  std::cout << '\n';

  // All data members
  std::cout << "data members:\n";
  for... (auto var : $S.variables())
    std::cout << var.type().name() << ' ' << var.qualified_name()
              << $var.type().name() << '\n';
  std::cout << '\n';

  // Non-static data members
  std::cout << "non-static data members:\n";
  for... (auto var : $S.member_variables())
    std::cout << var.type().name() << ' ' << var.qualified_name() << '\n';
  std::cout << '\n';

  // Static data members
  std::cout << "static data members:\n";
  for... (auto var : $S.static_variables())
    std::cout << var.type().name() << ' ' << var.qualified_name() << '\n';
  std::cout << '\n';

  // All function members
  std::cout << "member functions:\n";
  for... (auto fn : $S.functions())
    std::cout << fn.type().name() << ' ' << fn.qualified_name()
              << " : " << $fn.type().name() << '\n';
  std::cout << '\n';

  // Non-static member functions
  std::cout << "non-static member functions:\n";
  for... (auto fn : $S.member_functions())
    std::cout << fn.type().name() << ' ' << fn.qualified_name() << '\n';
  std::cout << '\n';

  // Static data members
  std::cout << "static member functions:\n";
  for... (auto fn : $S.static_functions())
    std::cout << fn.type().name() << ' ' << fn.qualified_name() << '\n';
}
