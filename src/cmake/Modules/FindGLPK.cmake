FIND_PATH(GLPK_INCLUDE_DIR NAMES glpk.h PATHS
    /usr/local/include
    /usr/include/
    NO_DEFAULT_PATH)
FIND_LIBRARY(GLPK_LIBRARIES
    NAMES glpk
    PATHS /usr/local/lib
    /usr/lib)
if (GLPK_INCLUDE_DIR AND GLPK_LIBRARIES)
    set(GLPK_FOUND TRUE)
endif (GLPK_INCLUDE_DIR AND GLPK_LIBRARIES)
if (GLPK_FOUND)
    MESSAGE(STATUS "Looking for GLPK - found ${GLPK_LIBRARIES}")
else(GLPK_FOUND)
    MESSAGE(STATUS "Looking for GLPK - Not found")
endif (GLPK_FOUND)

# Set (NAME)_FOUND if all the variables and the version are satisfied.
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GLPK
    FAIL_MESSAGE  DEFAULT_MSG
    REQUIRED_VARS GLPK_INCLUDE_DIRS GLPK_LIBRARIES)
