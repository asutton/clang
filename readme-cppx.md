
### Information about the extensions in this fork of Clang

## Prototype compiler

Online: https://cppx.godbolt.org 

Source: https://github.com/asutton/clang 

### Documentation

The current proposal document [P0707R1](https://herbsutter.files.wordpress.com/2017/07/p0707r1.pdf) contains the current "what it is" writeup with technical overview.

The [<meta> header](https://github.com/asutton/clang/blob/master/tools/libcppx/include/cppx/meta) contains the things you can query (e.g., .variables(), .member_variables()) and do (e.g., make_pure_virtual()).

The [<compiler> header](https://github.com/asutton/clang/blob/master/tools/libcppx/include/cppx/compiler) contains the compiler.error(), .require(), and .debug().


### Examples

The primary set of examples is in [/tools/libcppx/examples](https://github.com/asutton/clang/tree/master/tools/libcppx/examples).

Additionally, the P0707 paper contains the following examples linked to the online live compiler:

  - [interface](https://godbolt.org/g/Uzw5iJ)
  - [base_class](https://godbolt.org/g/sXmhkN)
  - [value](https://godbolt.org/g/59LSSZ) (regular type)
  - [plain_struct](https://godbolt.org/g/2uMpF5)

