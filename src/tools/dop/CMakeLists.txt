SET(DOP_SRCS "${DOP_SRCS}"
  "${CMAKE_CURRENT_LIST_DIR}/dopconfig.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/print.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/print_latex.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/print_py.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/process.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/var_map.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/visualize.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/parsers/dop/pstate.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/parsers/dop/stacks.cpp"
  "${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc"
  "${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc"

  PARENT_SCOPE)
add_subdirectory(parsers/baron)
