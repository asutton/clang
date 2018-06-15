// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>

#include <iostream>
#include <string>
#include <vector>

// Just make sure we don't break any existing code.

int main() {
  return 0;
}