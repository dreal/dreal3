SET(DREAL_SRCS ${DREAL_SRCS}
  ${CMAKE_CURRENT_LIST_DIR}/Cnfizer.C
  ${CMAKE_CURRENT_LIST_DIR}/Tseitin.C
  PARENT_SCOPE)
# add_library(opensmt_cnfizers Cnfizer.C Tseitin.C)
# target_link_libraries(opensmt_cnfizers util)
