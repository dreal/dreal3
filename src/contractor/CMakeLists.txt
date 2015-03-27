SET(DREAL_SRCS ${DREAL_SRCS}
  ${CMAKE_CURRENT_LIST_DIR}/contractor_basic.cpp
  ${CMAKE_CURRENT_LIST_DIR}/contractor_ibex.cpp
  ${CMAKE_CURRENT_LIST_DIR}/contractor_capd4.cpp
  PARENT_SCOPE)
# add_library(contractor
#   contractor_basic.cpp
#   contractor_ibex.cpp
#   contractor_capd4.cpp
#   )
# add_dependencies(contractor CAPD4)
# add_dependencies(contractor IBEX)
# add_dependencies(contractor JSON11)
# add_dependencies(contractor util)
