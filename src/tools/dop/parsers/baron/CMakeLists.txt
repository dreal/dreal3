# # Create custom command for flex/lex (note the outputs)
# ADD_CUSTOM_COMMAND(
#   COMMAND ${FLEX_EXECUTABLE}
#   ARGS -o ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc -Pbaron
#   ${DREAL_SOURCE_DIR}/tools/dop/parsers/baron/baronlexer.ll
#   DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/baron/baronlexer.ll
#   OUTPUTS ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc
#   )

# # Create custom command for bison/yacc (note the DEPENDS)
# ADD_CUSTOM_COMMAND(
#   COMMAND ${BISON_EXECUTABLE}
#   ARGS -d --name-prefix=baron -y ${DREAL_SOURCE_DIR}/tools/dop/parsers/baron/baronparser.yy
#   -o ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc
#   DEPENDS ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc
#   DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/baron/baronparser.yy
#   OUTPUTS ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc
#   )

# SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc GENERATED)
# SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc GENERATED)

# # Include binary directory to include lexer.c in parser.c
INCLUDE_DIRECTORIES(${DREAL_BINARY_DIR}/tools/dop/parsers/baron)

SET(DOP_SRCS ${DOP_SRCS}
  ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc
  ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc
  PARENT_SCOPE)

# add_library(opensmt_baronparser baronparser.cc baronlexer.cc)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-sign-compare")
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-null-conversion -Wno-unneeded-internal-declaration -Wno-deprecated-register")
endif ()
# target_link_libraries(opensmt_baronparser util)
