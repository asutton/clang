// RUN: %clang -std=c++1z %s 

struct tup { };

namespace std
{
  template<typename T>
  struct tuple_size;

  template<>
  struct tuple_size<::tup> { static constexpr int value = 1; };
}

template<int I> int get(tup) { return 0; }

void f1()
{
  for... (auto x : tup{}) {
    auto y = x;
    (void)(y + 3);
  }
}

template<typename T>
void f2()
{
  for... (auto x : T{}) {
    auto y = x;
    (void)(y + 3);
  }
}

int main() {
  f1();
  f2<tup>();
}