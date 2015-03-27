SET(DREAL_SRCS ${DREAL_SRCS}
  ${CMAKE_CURRENT_LIST_DIR}/opensmt_c.C
  ${CMAKE_CURRENT_LIST_DIR}/OpenSMTContext.C
  PARENT_SCOPE)

# add_library(opensmt_api opensmt_c.C OpenSMTContext.C)
# target_link_libraries(opensmt_api util)
# add_dependencies(opensmt_api CAPD4)
# add_dependencies(opensmt_api JSON11)
