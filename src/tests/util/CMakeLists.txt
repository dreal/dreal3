add_executable(box box.cpp)
target_link_libraries(box dreal gtest ${EXTRA_LIBS})
add_test(box ${CMAKE_CURRENT_BINARY_DIR}/box)
