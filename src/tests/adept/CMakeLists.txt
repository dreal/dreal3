add_executable(test_adept test_adept.cpp)
target_link_libraries(test_adept dreal ${EXTRA_LIBS})
add_test(test_adept ${CMAKE_CURRENT_BINARY_DIR}/test_adept)
