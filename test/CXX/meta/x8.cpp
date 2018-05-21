// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

using HRESULT = long;

template<typename T>
constexpr void gen_impl(T proto)
{
  for... (auto var : proto.member_variables()) {
    var.make_private();
    __generate var;
  }

  // Copy member functions as public:
  for...(auto fn : proto.member_functions()) {
    fn.make_public();
    __generate fn;
  }
}

template<typename T>
constexpr void gen_void_fn(T fn)
{
  __generate struct {
    virtual HRESULT idexpr(fn)(__inject(fn.parameters())) {
      this->m_impl.idexpr(fn)();
      return HRESULT();
    }

    // template<typename... Args>
    // HRESULT idexpr(fn)(Args&&... args) {
    //   this->m_impl.idexpr(fn)();
    // }
  };
}

template<typename T>
constexpr void gen_non_void_fn(T fn)
{
  auto ret = fn.return_type();
  __generate struct {
    virtual HRESULT idexpr(fn)(typename(ret)* retval);
  };
}

template<typename T>
constexpr void rt_class(T proto)
{
  // Create the implementation class. 
  __generate __fragment class {
    class impl_type {
      constexpr { gen_impl(proto); }
    };
  };

  // Generate a member of the type.
  __generate __fragment class C {
    typename C::impl_type m_impl;
  };

  // Generate wrappers that call into the implementation.
  for... (auto fn : proto.member_functions()) {
    auto ret = fn.return_type();
    if (ret == $void)
      gen_void_fn(fn);
    else
      gen_non_void_fn(fn);
  }
}

class(rt_class) Circle {
  int data1, data2;
  int f(int i, int j) { return i+j; }
  int g(double d) { return (int)d; }
  void h() { return; }
};

constexpr {
  meta::compiler.debug($Circle);
}

int main() { 
  Circle c;

  c.h();

  // int ret;
  // c.f(&ret);
}



  // Add the wrapper functions under a public umbrella.
  // __extend(out) struct {
  // public:
  // };
  // for... (auto f : in.member_functions()) {
  //   auto ret = f.return_type();
  //   if (ret == $void) {
  //     __extend(out) class {
  //       virtual HRESULT idexpr(f)(__inject(f.parameters()));
  //     };
  //   } 
  //   else {
  //     __extend(out) class {
  //       virtual HRESULT idexpr(f)(__inject(f.parameters()), typename(ret)* retval);
  //     };
  //   }
  // }
// }
