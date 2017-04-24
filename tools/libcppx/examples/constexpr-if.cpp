#include <cppx/meta>
#include <iostream>

using namespace cppx::meta;

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
  for... (auto x : $S.members()) {
    // Note that this could also be a normal "if" statement.
    if constexpr (is_member_variable(x))
      std::cout << "member variable: " << x.name() << '\n';
    else if constexpr (is_member_function(x))
      std::cout << "member function: " << x.name() << '\n';
  }
  
}
