// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

enum E {
  A, B, C
};

 // Namespace injection

constexpr {
  int n = 0;
  for... (auto x : $E.members()) {
    __generate namespace N {
      const int idexpr("x", n) = n;
    };
    ++n;
  }
} // constexpr

static_assert(x0 == 0);
static_assert(x1 == 1);
static_assert(x2 == 2);

int n = x0;

// Direct class injection

struct S1 {
  constexpr {
    auto f1 = __fragment struct C {
      C* next;
    };
    __generate f1;
  } // constexpr
};

// Indirect class injection

constexpr void make_pointers() {
  __generate struct S {
    S* p1;
    S* p2;
  };
}

struct S2 {
  constexpr { make_pointers(); }
};

// Injecting member functions

constexpr void make_getters() {
  __generate struct S {
    int get_external() const { return this->n; }

    int local;
    int get_local() const { return this->local; }

    // FIXME: When this is instantiated, we will have lost injection context 
    // that provides the replacement of 'this' with its the injectee. In other 
    // words, this won't be resolved correctly.
    //
    // Actually, it looks like this is being 'local' is being created as
    // a MemberExpr, when it should be CXXDependentScopeMemberExpr. That's
    // the difference between this function and the one above.
    //
    // For now, write this-> to ensure explicit replacement.
    int get_local_err() const { return local; }

    // FIXME: This currently fails. But... here's an interesting problem.
    // If you introduce local variables through an injection, how do you
    // initialize them in the derived class? We should allow constructors
    // that initialize members as part as a kind of sub-object.
    //
    // Of course, we would then require destructors to do the same.
    //
    // The implication would be that neither constructors nor destructors
    // are injected, but in fact VERY special in these contexts. 

    // int err = 42;
  };
}

struct S3 {
  S3() {
    local = 42;
  }
  int n = 12;
  constexpr { make_getters(); }
};


// Test with templates.

template<typename T>
constexpr auto f2() {
  return __fragment class {
    T a;
    T b;
  };
}

struct S4 {
  constexpr {
    __generate f2<int>();
  }
};

template<typename T>
struct S5 {
  constexpr {
    __generate f2<T>();
  }
};

int main() { 
  compiler.debug($S1);
  compiler.debug($S2);

  // FIXME: This isn't printing member functions. Why not? However, they
  // clearly exist: see below.
  compiler.debug($S3);

  S3 x;
  assert(x.get_external() == 12);
  assert(x.get_local() == 42);

  compiler.debug($S4);
  compiler.debug($S5<int>); //  Not instantiated, won't show def. Should it?
  S5<char> s5;
  compiler.debug($S5<char>); // Fully instantiated.
}
