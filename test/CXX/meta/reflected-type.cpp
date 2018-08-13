// RUN: %clang -c -g -std=c++1z -Xclang -freflection %s 

// This test checks an error when reflected types are not
// being unwrapped to emit debug information.

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

//====================================================================
// Library code: implementing the metaclass function (once)

using HRESULT = unsigned long;

template<typename T>
constexpr void my_metaclass(T source) {
    for... (auto f : source.member_functions()) {
        __generate f;       // generate original function
        auto ret = f.return_type();   // now generate wrapper
        if (ret == $void) 
            __generate struct {
                HRESULT idexpr(f)(__inject(f.parameters()) args, int)
                    { this->idexpr(f)(args...); return 0; }
            };
        else 
            __generate struct {
                HRESULT idexpr(f)(__inject(f.parameters()) args, typename(ret)* retval)
                    { *retval = this->idexpr(f)(args...); return 0; }
            };
    }
}

//====================================================================
// User code: using the metaclass to write a type (many times)

class(my_metaclass) Circle {
  int g(double d) { return (int)d; }
  void h() { return; }
  int f(int i, int j) { return i+j; }
};

// Compiler Explorer note: Click the "triangle ! icon" to see the output:
constexpr {
  compiler.debug($Circle);
}

int main() { 
  Circle c;
}
