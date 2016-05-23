add_executable(capd4_example_01 example_01.cpp)
target_link_libraries(capd4_example_01 dreal ${EXTRA_LIBS})
add_test(capd4_example_01 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_01)

add_executable(capd4_example_02 example_02.cpp)
target_link_libraries(capd4_example_02 dreal ${EXTRA_LIBS})
add_test(capd4_example_02 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_02)

add_executable(capd4_example_03 example_03.cpp)
target_link_libraries(capd4_example_03 dreal ${EXTRA_LIBS})
add_test(capd4_example_03 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_03)

add_executable(capd4_example_04 example_04.cpp)
target_link_libraries(capd4_example_04 dreal ${EXTRA_LIBS})
add_test(capd4_example_04 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_04)

add_executable(capd4_example_05 example_05.cpp)
target_link_libraries(capd4_example_05 dreal ${EXTRA_LIBS})
add_test(capd4_example_05 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_05)

add_executable(capd4_example_06 example_06.cpp)
target_link_libraries(capd4_example_06 dreal ${EXTRA_LIBS})
add_test(capd4_example_06 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_06)

add_executable(capd4_example_07 example_07.cpp)
target_link_libraries(capd4_example_07 dreal ${EXTRA_LIBS})
add_test(capd4_example_07 ${CMAKE_CURRENT_BINARY_DIR}/capd4_example_07)

add_executable(capd4_sol sol.cpp)
target_link_libraries(capd4_sol dreal ${EXTRA_LIBS})
add_test(capd4_sol ${CMAKE_CURRENT_BINARY_DIR}/capd4_sol)

add_executable(capd4_nonrigor_sol nonrigor_sol.cpp)
target_link_libraries(capd4_nonrigor_sol dreal ${EXTRA_LIBS})
add_test(capd4_nonrigor_sol ${CMAKE_CURRENT_BINARY_DIR}/capd4_nonrigor_sol)
