
cmake_minimum_required(VERSION 3.5)

project(cppx CXX)

include_directories(include)

install(DIRECTORY include/cppx DESTINATION include)

add_subdirectory(include/cppx)

# Don't build examples as part of the main build.
# add_subdirectory(examples)
