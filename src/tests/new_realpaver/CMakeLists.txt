add_executable(newrp_interval interval.cpp)
target_link_libraries(newrp_interval ${EXTRA_LIBS})
add_test(newrp_interval ${CMAKE_CURRENT_BINARY_DIR}/newrp_interval)

add_executable(newrp_unionInterval unionInterval.cpp)
target_link_libraries(newrp_unionInterval ${EXTRA_LIBS})
add_test(newrp_unionInterval ${CMAKE_CURRENT_BINARY_DIR}/newrp_unionInterval)
