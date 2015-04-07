add_subdirectory(api)
add_subdirectory(cnfizers)
add_subdirectory(common)
add_subdirectory(egraph)
add_subdirectory(minisat)
add_subdirectory(parsers/smt2)
add_subdirectory(simplifiers)
add_subdirectory(smtsolvers)
add_subdirectory(sorts)
add_subdirectory(tsolvers)

SET(DREAL_SRCS "${DREAL_SRCS}" "${CMAKE_CURRENT_LIST_DIR}/global.cpp"
  PARENT_SCOPE)

# add_library(opensmt ${DREAL_SRCS})
# target_link_libraries(opensmt util)
# add_dependencies(opensmt CAPD4)
# add_dependencies(opensmt JSON)
