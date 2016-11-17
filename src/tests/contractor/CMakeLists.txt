add_executable(contractor_ibex contractor_ibex.cpp)
target_link_libraries(contractor_ibex dreal ${EXTRA_LIBS})
add_test(contractor_ibex ${CMAKE_CURRENT_BINARY_DIR}/contractor_ibex)

if(SUPPORT_ODE)
    add_executable(contractor_capd contractor_capd.cpp)
    target_link_libraries(contractor_capd dreal ${EXTRA_LIBS})
    add_test(contractor_capd ${CMAKE_CURRENT_BINARY_DIR}/contractor_capd)
endif()
