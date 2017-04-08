
#include <iostream>

#include <cpp3k/meta>

namespace meta = cpp3k::meta;

template<typename E> // requires Enum<E>
struct select_name {
  E target;
  char const*& result;

  template<typename T> // requires Enumerator<T>
  void operator()(T enumerator) const {
    if (enumerator.value() == target)
      result = enumerator.name();
  }
};


template<typename E> // Enum E
std::enable_if_t<std::is_enum_v<E>, char const*>
to_string(E value) {
  char const* name = nullptr;
  meta::for_each($E.members(), select_name<E>{value, name});
  return name;
}


// A simple enum
enum E {
  A, B, C
};

int main() {
  std::cout << to_string(A) << '\n';
  std::cout << to_string(B) << '\n';
  std::cout << to_string(C) << '\n';
}
