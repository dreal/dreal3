add_executable(capd3_example_01 example_01.cpp)
target_link_libraries(capd3_example_01 dreal ${EXTRA_LIBS})
add_test(capd3_example_01 ${CMAKE_CURRENT_BINARY_DIR}/capd3_example_01)

add_executable(capd3_example_02 example_02.cpp)
target_link_libraries(capd3_example_02 dreal ${EXTRA_LIBS})
add_test(capd3_example_02 ${CMAKE_CURRENT_BINARY_DIR}/capd3_example_02)
