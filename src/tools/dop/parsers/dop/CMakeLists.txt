# # Create custom command for flex/lex (note the outputs)
# ADD_CUSTOM_COMMAND(
#   COMMAND ${FLEX_EXECUTABLE}
#   ARGS -o ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc -Pdop
#   ${DREAL_SOURCE_DIR}/tools/dop/parsers/dop/doplexer.ll
#   DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/dop/doplexer.ll
#   OUTPUTS ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc
#   )

# # Create custom command for bison/yacc (note the DEPENDS)
# ADD_CUSTOM_COMMAND(
#   COMMAND ${BISON_EXECUTABLE}
#   ARGS -d --name-prefix=dop -y ${DREAL_SOURCE_DIR}/tools/dop/parsers/dop/dopparser.yy
#   -o ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/dopparser.cc
#   DEPENDS ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc
#   DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/dop/dopparser.yy
#   OUTPUTS ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/dopparser.cc
#   )

# SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/dop/dopparser.cc GENERATED)
# SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc GENERATED)

# # Include binary directory to include lexer.c in parser.c
INCLUDE_DIRECTORIES(${DREAL_BINARY_DIR}/tools/dop/parsers/dop)

SET(DOP_SRCS ${DOP_SRCS}
  ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/dopparser.cc
  ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc
  PARENT_SCOPE)

# add_library(opensmt_dopparser dopparser.cc doplexer.cc)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-sign-compare")
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-null-conversion -Wno-unneeded-internal-declaration -Wno-deprecated-register")
endif ()
# target_link_libraries(opensmt_dopparser util)
