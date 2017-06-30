// RUN: echo

#include <cppx/meta>
#include <cppx/compiler>

struct S {
  S() = default;
  int x;
};

using namespace cppx::meta;
$class basic_value {
  basic_value() = default;
  basic_value(const basic_value& that)            = default;
  basic_value(basic_value&& that)                 = default;
  basic_value& operator=(const basic_value& that) = default;
  basic_value& operator=(basic_value&& that)      = default;

  // Check members
  constexpr {
    for... (auto f : $basic_value.member_functions()) {
      compiler.require(!f.is_virtual(),   "a value type may not have a virtual function");
      compiler.require(!f.is_protected(), "a value type may not have a protected function");
      compiler.require(!f.is_destructor() || f.is_public(), "a value destructor must be public");
    }
  } // end metaprogram

  // Transform members
  constexpr {
    access_kind mode = default_access;
    for... (auto m : $basic_value.members()) {
      if (mode == default_access) {
        if constexpr (m.is_member_variable())
          m.make_private();
        if constexpr (m.is_member_function())
          m.make_public();
        if constexpr (m.is_access_specifier())
          mode = m.access();
      }
    }
  } // end metaprogram
};


$class comparable {
  bool operator==(const comparable& that) const {
    return true;
  }
  bool operator!=(const comparable& that) const {
    return false;
  }
};

$class ordered : comparable {
  bool operator<(const ordered& that) const {
    return false;
  }
  bool operator>(const ordered& that) const {
    return false;
  }
  bool operator<=(const ordered& that) const {
    return false;
  }
  bool operator>=(const ordered& that) const {
    return false;
  }
};

$class regular : basic_value, comparable { };

$class value : basic_value, ordered { };


value foo {
  int a;
public:
  int b;
private:
  void f() { }
};

int main() {
  compiler.debug($foo);
  foo f1;
  foo f2 = f1;
  // (void)f1.a; // error: private
  (void)f1.b; // Ok
  // (void)f1.f() // error: private
}
