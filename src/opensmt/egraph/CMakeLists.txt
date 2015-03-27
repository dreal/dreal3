SET(DREAL_SRCS ${DREAL_SRCS}
  ${CMAKE_CURRENT_LIST_DIR}/EgraphDTC.C
  ${CMAKE_CURRENT_LIST_DIR}/EgraphDebug.C
  ${CMAKE_CURRENT_LIST_DIR}/EgraphExplain.C
  ${CMAKE_CURRENT_LIST_DIR}/EgraphSolver.C
  ${CMAKE_CURRENT_LIST_DIR}/EgraphStore.C
  ${CMAKE_CURRENT_LIST_DIR}/Enode.C
  ${CMAKE_CURRENT_LIST_DIR}/SigTab.C
  PARENT_SCOPE)
# add_library(opensmt_egraph EgraphSolver.C EgraphStore.C EgraphExplain.C EgraphDTC.C EgraphDebug.C Enode.C SigTab.C)
# target_link_libraries(opensmt_egraph util)
# add_dependencies(opensmt_egraph CAPD4)
# add_dependencies(opensmt_egraph JSON11)