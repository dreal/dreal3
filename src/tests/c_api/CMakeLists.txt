add_executable(c_api_example_01 example_01.c)
target_link_libraries(c_api_example_01 ${DREAL_LIBS} ${EXTRA_LIBS})
add_test(c_api_example_01 ${CMAKE_CURRENT_BINARY_DIR}/c_api_example_01)
