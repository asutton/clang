
#include <cstdint>
#include <iostream>
#include <iomanip>
#include <vector>

#include <cpp3k/meta>

namespace meta = cpp3k::meta;

// Pretend to be a hashing algorithm.
struct hasher
{
  void operator()(void const* p, int n)
  {
    char const* q = reinterpret_cast<char const*>(p);
    while (n) {
      bytes.push_back(*q);
      ++q;
      --n;
    }
  }
  std::vector<std::uint8_t> bytes;
};


template<typename H, typename T>
std::enable_if_t<std::is_integral<T>::value, void>
hash_append(H& hash, T n)
{
  hash(&n, sizeof(T));
}

template<typename H, typename T>
std::enable_if_t<std::is_floating_point<T>::value, void>
hash_append(H& hash, T n)
{
  if (n == 0)
    n = 0;
  hash(&n, sizeof(T));
}


template<typename H, typename T>
struct hash_append_fn
{
  H& h;
  T const& t;
  template<cpp3k::meta::reflection_t X>
  void operator()(cpp3k::meta::member_variable<X> var) {
    hash_append(h, t.*(var.pointer()));
  }
};


template<typename H, typename T>
std::enable_if_t<std::is_class<T>::value, void> 
hash_append(H& h, T const& t)
{
  meta::for_each($T.member_variables(), hash_append_fn<H, T>{h, t});
  
  // cpp3k::meta::tuple_for_each($T.member_variables(), [&h](auto const& t) {
  //   hash_append(h, t);
  // });
}

struct P {
  double d = 3.14;
};

struct S
{
  int first = 3;
  char second = 5;
  P fun;
};

int main()
{
  S s0;
  hasher h;
  hash_append(h, s0);

  std::cout << std::hex;
  std::cout << std::setfill('0');
  unsigned int n = 0;
  for (auto c : h.bytes) {
      std::cout << std::setw(2) << (unsigned)c << ' ';
      if (++n == 16) {
          std::cout << '\n';
          n = 0;
      }
  }
  std::cout << '\n';
  std::cout << std::dec;
  std::cout << std::setfill(' ');
}



