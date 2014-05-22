################################################################
# GIT HASH
################################################################
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file("${DREAL_SOURCE_DIR}/util/git_sha1.cpp.in" "${DREAL_BINARY_DIR}/git_sha1.cpp" @ONLY)
add_library(util
  hexfloat.cpp
  interval.cpp
  scoped_env.cpp
  scoped_vec.cpp
  string.cpp
  "${DREAL_BINARY_DIR}/git_sha1.cpp"
  "${DREAL_SOURCE_DIR}/util/git_sha1.h"
  )
target_link_libraries(util glog)
