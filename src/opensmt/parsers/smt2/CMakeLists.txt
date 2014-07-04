# Create target for the parser
ADD_CUSTOM_TARGET(SMT2Parser echo "Creating smt2parser.cc")

# Create custom command for flex/lex (note the outputs)
ADD_CUSTOM_COMMAND(
   COMMAND ${FLEX_EXECUTABLE}
   ARGS -o ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2lexer.cc -Psmt2
        ${DREAL_SOURCE_DIR}/opensmt/parsers/smt2/smt2lexer.ll
   DEPENDS ${DREAL_SOURCE_DIR}/opensmt/parsers/smt2/smt2lexer.ll
   OUTPUT ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2lexer.cc)

# Create custom command for bison/yacc (note the DEPENDS)
ADD_CUSTOM_COMMAND(
   COMMAND ${BISON_EXECUTABLE}
   ARGS -d --name-prefix=smt2 -y ${DREAL_SOURCE_DIR}/opensmt/parsers/smt2/smt2parser.yy
        -o ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2parser.cc
   DEPENDS ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2lexer.cc
   DEPENDS ${DREAL_SOURCE_DIR}/opensmt/parsers/smt2/smt2parser.yy
   OUTPUT ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2parser.cc)

# Add parser.c to the list of sources
SET(DREAL_SRCS ${DREAL_SRCS} ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2parser.cc)

# Since parser.c does not exists yet when cmake is run, mark
# it as generated
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2parser.cc GENERATED)

# Include binary directory to include lexer.c in parser.c
INCLUDE_DIRECTORIES(${DREAL_BINARY_DIR}/opensmt/parsers/smt2)

add_library(opensmt_smt2parser smt2parser.cc smt2lexer.cc)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-sign-compare")
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-null-conversion -Wno-unneeded-internal-declaration -Wno-deprecated-register")
endif ()
target_link_libraries(opensmt_smt2parser util)
