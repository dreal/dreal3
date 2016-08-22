add_executable(box box.cpp)
target_link_libraries(box dreal ${EXTRA_LIBS})
add_test(box ${CMAKE_CURRENT_BINARY_DIR}/box)

if(COMP_HAS_THREAD_LOCAL)
    add_executable(tls_box tls_box.cpp)
    target_link_libraries(tls_box dreal ${EXTRA_LIBS})
    add_test(tls_box ${CMAKE_CURRENT_BINARY_DIR}/tls_box)
endif()
