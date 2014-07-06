add_executable(interval interval.cpp)
target_link_libraries(interval ${EXTRA_LIBS})
add_test(rp_interval ${CMAKE_CURRENT_BINARY_DIR}/interval)
