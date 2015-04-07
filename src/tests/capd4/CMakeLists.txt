add_executable(capd4_example_01 example_01.cpp)
target_link_libraries(capd4_example_01 dreal ${EXTRA_LIBS} gtest)
add_test(capd4_example_01 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_01)
