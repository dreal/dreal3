################################################################
# GIT HASH
################################################################
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file("${DREAL_SOURCE_DIR}/util/git_sha1.cpp.in" "${DREAL_BINARY_DIR}/git_sha1.cpp" @ONLY)
add_library(util
  box.cpp
  constraint.cpp
  flow.cpp
  ibex_enode.cpp
  stat.cpp
  string.cpp
  "${DREAL_BINARY_DIR}/git_sha1.cpp"
  "${DREAL_SOURCE_DIR}/util/git_sha1.h"
  )
add_dependencies(util GLOG)
add_dependencies(util GFLAGS)
