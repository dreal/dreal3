add_executable(capd4_example_01 example_01.cpp)
target_link_libraries(capd4_example_01 dreal ${EXTRA_LIBS})
add_test(capd4_example_01 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_01)

add_executable(capd4_example_02 example_02.cpp)
target_link_libraries(capd4_example_02 dreal ${EXTRA_LIBS})
add_test(capd4_example_02 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_02)

add_executable(capd4_example_03 example_03.cpp)
target_link_libraries(capd4_example_03 dreal ${EXTRA_LIBS})
add_test(capd4_example_03 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_03)
