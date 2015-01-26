add_library(dsolvers nra_solver.cpp)
add_dependencies(dsolvers JSON11)
target_link_libraries(dsolvers ${DREAL_LIBS} ${EXTRA_LIBS})
