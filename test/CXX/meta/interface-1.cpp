// RUN: %clang -c -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

//====================================================================
// Library code: implementing the metaclass (once)

template<typename T>
constexpr void interface(T source) {

   compiler.require(source.variables().empty(),
      "interfaces may not contain data");

   for... (auto f : source.functions()) {

      compiler.require(!f.is_copy() && !f.is_move(),
         "interfaces may not copy or move; consider"
         " a virtual clone() instead");

      if (!f.has_default_access()) f.make_public();
      compiler.require(f.is_public(),
         "interface functions must be public");

      f.make_pure_virtual();
      __generate f;
   }

   __generate __fragment struct X { virtual ~X() noexcept {} };
};


//====================================================================
// User code: using the metaclass to write a type (many times)

struct(interface) Shape {
    int area() const;
    void scale_by(double factor);
};

class X : Shape {
    int area() const { return 42; }
    void scale_by(double factor) { }
};

int main() {
    X x;
}

// Compiler Explorer note: Click the "triangle ! icon" to see the output:
constexpr {
    compiler.debug($Shape);
    compiler.debug($X);
}
