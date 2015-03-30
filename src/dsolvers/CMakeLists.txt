SET(DREAL_SRCS ${DREAL_SRCS}
  ${CMAKE_CURRENT_LIST_DIR}/nra_solver.cpp
  PARENT_SCOPE)

# add_library(dsolvers nra_solver.cpp)
# add_dependencies(dsolvers JSON)
# target_link_libraries(dsolvers dreal ${EXTRA_LIBS})
