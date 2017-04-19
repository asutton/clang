if(NOT LIBCPPX_BUILD_EXAMPLES)
  set_directory_properties(PROPERTIES EXCLUDE_FROM_ALL ON)
endif()

# Link all subsequently created targets against the 'cppx' library target.
# This is required to propagate transitive usage requirements.
# NOTE: Since 'cppx' is an interface library, no linking will actually occur.
link_libraries(cppx)

#.rst:
# .. command:: add_example
#
#    ::
#
#      add_example(NAME <name> SOURCES source1 [source2...]
#                  [WIN32] [MACOSX_BUNDLE] [EXCLUDE_FROM_ALL])
#
#    A convenience macro for adding an example program to the project.
#
#    Supported options:
#
#    ``NAME``
#      The name of the executable target that is added to the project.
#    ``SOURCES``
#      Specifies a list of source files to be passed to the
#      :command:`add_executable` command.
#    ``WIN32``
#      Corresponds to the ``WIN32`` option for the :command:`add_executable`
#      command.
#    ``MACOSX_BUNDLE``
#      Corresponds to the ``MACOSX_BUNDLE`` option for the
#      :command:`add_executable` command.
#    ``EXCLUDE_FROM_ALL``
#      Corresponds to the ``EXCLUDE_FROM_ALL`` option for the
#      :command:`add_executable` command.
#
#    ::
#
#      add_example(source1 [source2...])
#
#    A shorter form of the above.
#
#    The name of the executable target is set to the name of the first source
#    file argument (sans file extension).
macro(ADD_EXAMPLE)
  set(options WIN32 MACOSX_BUNDLE EXCLUDE_FROM_ALL)
  set(oneValueArgs NAME)
  set(multiValueArgs SOURCES)

  cmake_parse_arguments(_ADD_EXAMPLE "${options}" "${oneValueArgs}"
    "${multiValueArgs}" ${ARGN})

  set(_ADD_EXAMPLE_ADD_WIN32)
  set(_ADD_EXAMPLE_ADD_MACOSX_BUNDLE)
  set(_ADD_EXAMPLE_ADD_EXCLUDE_FROM_ALL)

  if(NOT (DEFINED _ADD_EXAMPLE_NAME OR DEFINED _ADD_EXAMPLE_SOURCES))
    if(${ARGC} EQUAL 0)
      message(FATAL_ERROR "ADD_EXAMPLE() called with incorrect number of arguments.")
    endif()
    # Parse arguments for alternate signature.
    get_filename_component(_ADD_EXAMPLE_NAME ${ARGV0} NAME_WE)
    set(_ADD_EXAMPLE_SOURCES ${ARGV})
  else()
    if(DEFINED _ADD_EXAMPLE_UNPARSED_ARGUMENTS)
      message(FATAL_ERROR "ADD_EXAMPLE() given unknown keywords \"${_ADD_EXAMPLE_UNPARSED_ARGUMENTS}\".")
    endif()
    if(_ADD_EXAMPLE_WIN32)
      set(_ADD_EXAMPLE_ADD_WIN32 WIN32)
    endif()
    if(_ADD_EXAMPLE_MACOSX_BUNDLE)
      set(_ADD_EXAMPLE_ADD_MACOSX_BUNDLE MACOSX_BUNDLE)
    endif()
    if(_ADD_EXAMPLE_EXCLUDE_FROM_ALL)
      set(_ADD_EXAMPLE_ADD_EXCLUDE_FROM_ALL EXCLUDE_FROM_ALL)
    endif()
  endif()

  if(_ADD_EXAMPLE_NAME STREQUAL "")
    message(FATAL_ERROR "ADD_EXAMPLE() must be given non-empty NAME.")
  endif()
  if(_ADD_EXAMPLE_SOURCES STREQUAL "")
    message(FATAL_ERROR "ADD_EXAMPLE() must be given non-empty SOURCES.")
  endif()

  # Add example program as an executable target.
  add_executable(${_ADD_EXAMPLE_NAME}
    ${_ADD_EXAMPLE_ADD_WIN32} ${_ADD_EXAMPLE_ADD_MACOSX_BUNDLE}
    ${_ADD_EXAMPLE_ADD_EXCLUDE_FROM_ALL} ${_ADD_EXAMPLE_SOURCES})
  # Group all example program targets together in generated IDE projects.
  set_target_properties(${_ADD_EXAMPLE_NAME} PROPERTIES FOLDER "Examples")
endmacro()

add_example(logging.cpp)
add_example(logging2.cpp)
add_example(equal.cpp)
add_example(hash.cpp)
add_example(enum.cpp)
