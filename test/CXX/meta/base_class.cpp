// RUN: echo

#include <cppx/meta>
#include <cppx/compiler>

// #include <iostream>

using namespace cppx::meta;


$class base_class {
  constexpr {
    for... (auto f : $base_class.functions()) {
      if (f.is_destructor() && 
          !(f.is_public() && f.is_virtual()) && 
          !(f.is_protected() && !f.is_virtual()))
        compiler.error("base class destructors must be public and "
                       "virtual, or protected and nonvirtual");
      
      if (f.is_copy() || f.is_move())
        compiler.error("base classes may not copy or move; "
                       " consider a virtual clone() instead");
      }
      
      for... (auto b : $base_class.bases()) {
        compiler.require(b.is_public(), "non public base class");
        
        // NOTE: We haven't implement "is", and Clang does not permit the 
        // modification of an access specifier after it was created. This
        // is an artifact of the "modify in place" approach. This should be
        // implementable pending 

        // if (b.is(interface) && !b.has_access())
        //   f.make_public();
      }
      
      if (!$base_class.variables().empty())
        compiler.error("pure base classes may not contain data");
  }
};


struct canvas {

};

struct drawable {
  virtual void draw(canvas& c) = 0;
};

base_class shape : drawable {
  void draw(canvas& c) override { /*...*/ }
};

// base_class rectangle : private shape { // error: non-public base
//   void draw(canvas& c) override { /*...*/ }
// };

int main() {
  compiler.debug($shape);
}

