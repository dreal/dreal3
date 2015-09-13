SET(DOP_SRCS "${DOP_SRCS}"
  "${CMAKE_CURRENT_LIST_DIR}/dopconfig.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/print.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/print_latex.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/print_py.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/process.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/var_map.cpp"
  "${CMAKE_CURRENT_LIST_DIR}/visualize.cpp"
  "${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc"
  "${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc"
  "${DREAL_BINARY_DIR}/tools/dop/parsers/dop/dopparser.cc"
  "${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc"

  PARENT_SCOPE)
add_subdirectory(parsers/baron)
add_subdirectory(parsers/dop)
