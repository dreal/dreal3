add_executable(nlopt_example_01 example_01.cpp)
target_link_libraries(nlopt_example_01 dreal ${EXTRA_LIBS})
add_test(nlopt_example_01 ${CMAKE_CURRENT_BINARY_DIR}/nlopt_example_01)
