add_executable(json11_test_01 test_01.cpp)
target_link_libraries(json11_test_01 dreal ${EXTRA_LIBS})
add_test(json11_test_01 ${CMAKE_CURRENT_BINARY_DIR}/json11_test_01)

add_executable(json11_test_02 test_02.cpp)
target_link_libraries(json11_test_02 dreal ${EXTRA_LIBS})
add_test(json11_test_02 ${CMAKE_CURRENT_BINARY_DIR}/json11_test_02)
