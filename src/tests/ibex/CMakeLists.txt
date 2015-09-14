add_executable(ibex_example_01 example_01.cpp)
target_link_libraries(ibex_example_01 dreal ${EXTRA_LIBS})
add_test(ibex_example_01 ${CMAKE_CURRENT_BINARY_DIR}/ibex_example_01)

add_executable(ibex_example_02 example_02.cpp)
target_link_libraries(ibex_example_02 dreal ${EXTRA_LIBS})
add_test(ibex_example_02 ${CMAKE_CURRENT_BINARY_DIR}/ibex_example_02)

add_executable(ibex_example_03 example_03.cpp)
target_link_libraries(ibex_example_03 dreal ${EXTRA_LIBS})
add_test(ibex_example_03 ${CMAKE_CURRENT_BINARY_DIR}/ibex_example_03)

add_executable(ibex_example_04 example_04.cpp)
target_link_libraries(ibex_example_04 dreal ${EXTRA_LIBS})
add_test(ibex_example_04 ${CMAKE_CURRENT_BINARY_DIR}/ibex_example_04)

add_executable(ibex_defaultoptimizer defaultoptimizer.cpp)
target_link_libraries(ibex_defaultoptimizer dreal ${EXTRA_LIBS})
add_test(ibex_defaultoptimizer ${CMAKE_CURRENT_BINARY_DIR}/ibex_defaultoptimizer)
