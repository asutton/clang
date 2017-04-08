
set(LIBCPPX_HEADER_PATTERN
  PATTERN "*"
  PATTERN "CMakeLists.txt" EXCLUDE
  )

# FIXME: Don't do this if using an installed LLVM. See libcxx for
# the proper way to do this.
file(COPY .
  DESTINATION "${LLVM_BINARY_DIR}/include/cppx"
  FILES_MATCHING
  ${LIBCPPX_HEADER_PATTERN}
  )

install(DIRECTORY .
  DESTINATION include/cppx
  COMPONENT cppx-headers
  FILES_MATCHING
  ${LIBCPPX_HEADER_PATTERN}
  PERMISSIONS OWNER_READ OWNER_WRITE GROUP_READ WORLD_READ
  )
