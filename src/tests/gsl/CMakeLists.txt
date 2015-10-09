add_executable(gsl_ode_test ode_test.c)
target_link_libraries(gsl_ode_test dreal ${EXTRA_LIBS})
add_test(gsl_ode_test ${CMAKE_CURRENT_BINARY_DIR}/gsl_ode_test)
