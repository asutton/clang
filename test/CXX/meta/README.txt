
These tests don't work with the unit test environment. We need to copy some
of the set up from libcxx since these tests rely on both C++ headers and meta
headers, neither of which is included by default in this test suite's lit
configuration.
