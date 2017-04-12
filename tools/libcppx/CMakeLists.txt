cmake_minimum_required(VERSION 3.5)

project(cppx CXX)

add_subdirectory(include/cppx)

# Don't build examples as part of the main build.
# include_directories(include)
# add_subdirectory(examples)
