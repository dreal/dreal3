add_library(dsolvers nra_solver.cpp)
target_link_libraries(dsolvers ${DREAL_LIBS} ${EXTRA_LIBS})
