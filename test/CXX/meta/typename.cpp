// RUN: echo

void f1() {
  typename($int) n1;
  static_assert(__is_same(decltype(n1), int));
  typename($n1) n2;
  static_assert(__is_same(decltype(n2), int));
}

template<typename T, typename U>
void f2() {
  typename($T) n1;
  static_assert(__is_same(decltype(n1), U));
  typename($n1) n2;
  static_assert(__is_same(decltype(n2), U));
}

template<typename T>
struct S {
  static_assert(__is_same(T, int));
};

template<typename T>
void f3() {
  S<typename($T)> s;
}

int main() {
  f2<int, int>();
  S<typename($int)> s;
  f3<int>();
}
