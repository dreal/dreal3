if(SUPPORT_ODE)
  SET(DREAL_SRCS ${DREAL_SRCS}
    ${CMAKE_CURRENT_LIST_DIR}/contractor_basic.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_capd4.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_common.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_fixpoint.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_generic_forall.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_ibex.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_parallel.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_parallel_all.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_parallel_any.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_pseq.cpp
    PARENT_SCOPE)
else()
  SET(DREAL_SRCS ${DREAL_SRCS}
    ${CMAKE_CURRENT_LIST_DIR}/contractor_basic.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_ibex.cpp
    ${CMAKE_CURRENT_LIST_DIR}/contractor_generic_forall.cpp
    PARENT_SCOPE)
endif()
