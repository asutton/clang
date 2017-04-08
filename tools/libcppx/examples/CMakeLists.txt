cmake_minimum_required(VERSION 3.0)

# Find the cppk3 header file. Because the file is installed with Clang, we
# can simply assume that it will be in the header location configured by LLVM.
message(STATUS "Searching for <cpp3k/meta> header")
get_filename_component(LLVM_BINARY_DIR ${CMAKE_CXX_COMPILER} DIRECTORY)
execute_process(
  COMMAND ${LLVM_BINARY_DIR}/llvm-config --includedir
  OUTPUT_VARIABLE LLVM_INCLUDE_DIR)
string(STRIP ${LLVM_INCLUDE_DIR} LLVM_INCLUDE_DIR)

# Actually make sure the file exists at the configured location.
find_file(CPP3K_INCLUDE_FILE cpp3k/meta 
  NO_DEFAULT_PATH
  PATHS ${LLVM_INCLUDE_DIR})
if(CPP3K_INCLUDE_FILE-NOTFOUND)
  message(FATAL_ERROR "Cannot find header")
endif()
set(CPP3K_INCLUDE_DIR ${LLVM_INCLUDE_DIR})
message(STATUS "Found at ${CPP3K_INCLUDE_DIR}")


# Update the compiler directories.
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++1z -Xclang -freflection") 

include_directories(${LLVM_INCLUDE_DIR})

add_executable(logging logging.cpp)
add_executable(logging2 logging2.cpp)
add_executable(equal equal.cpp)
add_executable(hash hash.cpp)
add_executable(enum enum.cpp)
