SET(DREAL_SRCS ${DREAL_SRCS}
  ${CMAKE_CURRENT_LIST_DIR}/CoreSMTSolver.C
  ${CMAKE_CURRENT_LIST_DIR}/SimpSMTSolver.C
  ${CMAKE_CURRENT_LIST_DIR}/Proof.C
  ${CMAKE_CURRENT_LIST_DIR}/Debug.C
  ${CMAKE_CURRENT_LIST_DIR}/Theory.C
  ${CMAKE_CURRENT_LIST_DIR}/TheoryCombination.C
  ${CMAKE_CURRENT_LIST_DIR}/SMTConfig.C
  PARENT_SCOPE)
# add_library(opensmt_smtsolvers CoreSMTSolver.C SimpSMTSolver.C Proof.C Debug.C Theory.C TheoryCombination.C SMTConfig.C)
# target_link_libraries(opensmt_smtsolvers util gflags)
