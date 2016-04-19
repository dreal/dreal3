add_executable(glpk_example_01 example_01.cpp)
target_link_libraries(glpk_example_01 dreal ${EXTRA_LIBS})
add_test(glpk_example_01 ${CMAKE_CURRENT_BINARY_DIR}/glpk_example_01)

add_executable(glpk_example_02 example_02.cpp)
target_link_libraries(glpk_example_02 dreal ${EXTRA_LIBS})
add_test(glpk_example_02 ${CMAKE_CURRENT_BINARY_DIR}/glpk_example_02)
