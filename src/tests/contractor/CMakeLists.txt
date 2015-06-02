add_executable(ibex_fwdbwd ibex_fwdbwd.cpp)
target_link_libraries(ibex_fwdbwd dreal ${EXTRA_LIBS})
add_test(ibex_fwdbwd ${CMAKE_CURRENT_BINARY_DIR}/ibex_fwdbwd)
