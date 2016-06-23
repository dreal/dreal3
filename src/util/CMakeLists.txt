################################################################
# GIT HASH
################################################################
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file("${DREAL_SOURCE_DIR}/util/git_sha1.cpp.in" "${DREAL_BINARY_DIR}/git_sha1.cpp" @ONLY)

SET(DREAL_SRCS ${DREAL_SRCS}
  ${CMAKE_CURRENT_LIST_DIR}/box.cpp
  ${CMAKE_CURRENT_LIST_DIR}/cxx11_check.cpp
  ${CMAKE_CURRENT_LIST_DIR}/dtoa.c
  ${CMAKE_CURRENT_LIST_DIR}/eval.cpp
  ${CMAKE_CURRENT_LIST_DIR}/flow.cpp
  ${CMAKE_CURRENT_LIST_DIR}/fp.cpp
  ${CMAKE_CURRENT_LIST_DIR}/hexfloat.cpp
  ${CMAKE_CURRENT_LIST_DIR}/ibex_enode.cpp
  ${CMAKE_CURRENT_LIST_DIR}/proof.cpp
  ${CMAKE_CURRENT_LIST_DIR}/stat.cpp
  ${CMAKE_CURRENT_LIST_DIR}/string.cpp
  ${CMAKE_CURRENT_LIST_DIR}/interruptible_thread.cpp
  ${CMAKE_CURRENT_LIST_DIR}/strategy.cpp
  ${CMAKE_CURRENT_LIST_DIR}/subst_enode.cpp
  ${CMAKE_CURRENT_LIST_DIR}/glpk_wrapper.cpp
  "${DREAL_BINARY_DIR}/git_sha1.cpp"
  ${CMAKE_CURRENT_LIST_DIR}/git_sha1.h
  PARENT_SCOPE
  )
