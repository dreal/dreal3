add_executable(rp_interval interval.cpp)
target_link_libraries(rp_interval ${EXTRA_LIBS})
add_test(rp_interval ${CMAKE_CURRENT_BINARY_DIR}/rp_interval)
