add_executable(ibex_example_01 example_01.cpp)
target_link_libraries(ibex_example_01 dreal ${EXTRA_LIBS})
add_test(ibex_example_01 ${CMAKE_CURRENT_BINARY_DIR}/ibex_example_01)

add_executable(ibex_example_02 example_02.cpp)
target_link_libraries(ibex_example_02 dreal ${EXTRA_LIBS})
add_test(ibex_example_02 ${CMAKE_CURRENT_BINARY_DIR}/ibex_example_02)
