add_executable(z3_example example.cpp)
target_link_libraries(z3_example dreal ${EXTRA_LIBS})
add_test(z3_example ${CMAKE_CURRENT_BINARY_DIR}/z3_example)
