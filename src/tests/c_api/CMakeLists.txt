add_executable(c_api_example_01 example_01.c)
target_link_libraries(c_api_example_01 dreal ${EXTRA_LIBS} stdc++ gtest)
add_test(c_api_example_01 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_01)

add_executable(c_api_example_02 example_02.c)
target_link_libraries(c_api_example_02 dreal ${EXTRA_LIBS} stdc++ gtest)
add_test(c_api_example_02 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_02)
