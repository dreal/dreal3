INCLUDE_DIRECTORIES(${DREAL_BINARY_DIR}/tools/dop/parsers/baron)

SET(DOP_SRCS ${DOP_SRCS}
  ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc
  ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc
  PARENT_SCOPE)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-sign-compare")
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-null-conversion -Wno-unneeded-internal-declaration -Wno-deprecated-register")
endif ()
