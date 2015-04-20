add_executable(c_api_example_01 example_01.c)
target_link_libraries(c_api_example_01 dreal gtest ${EXTRA_LIBS} stdc++)
add_test(c_api_example_01 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_01)

add_executable(c_api_example_02 example_02.c)
target_link_libraries(c_api_example_02 dreal gtest ${EXTRA_LIBS} stdc++)
add_test(c_api_example_02 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_02)

add_executable(c_api_example_03 example_03.c)
target_link_libraries(c_api_example_03 dreal gtest ${EXTRA_LIBS} stdc++)
add_test(c_api_example_03 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_03)
