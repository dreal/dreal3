# - Try to find CLP
# Once done this will define
#  CLP_FOUND - System has CLP
#  CLP_INCLUDE_DIRS - The CLP include directories
#  CLP_LIBRARIES - The libraries needed to use CLP

find_package(PkgConfig)
# The result of `pkg-config clp --libs` includes "-lbz2" but Ubuntu
# package 'coinor-lib-dev' doesn't include libbz2-dev as a
# dependency. As a result, if you only do `sudo apt-get install
# coinor-clp-dev`, you will not have `libbz2-dev` installed and dReal
# won't compile since it can't find `-lbz2`.
find_package(BZip2 QUIET)
if (BZip2_FOUND)
    set(CLP_DEFINITIONS ${CLP_CFLAGS_OTHER})
    find_path(CLP_INCLUDE_DIR
        NAMES "ClpConfig.h"
        PATHS "/usr/include/coin"
        "/usr/local/include/clp/coin"
        NO_DEFAULT_PATH)
    get_filename_component(CLP_INCLUDE_DIR ${CLP_INCLUDE_DIR} DIRECTORY)
    set(CLP_INCLUDE_DIRS "${CLP_INCLUDE_DIRS};${CLP_INCLUDE_DIR}")
    include(FindPackageHandleStandardArgs)
    find_package_handle_standard_args(CLP DEFAULT_MSG CLP_INCLUDE_DIR CLP_LIBRARIES)
    mark_as_advanced(CLP_INCLUDE_DIR CLP_LIBRARIES )
endif()

if(CLP_FOUND)
    message(STATUS "Clp found (includes: ${CLP_INCLUDE_DIRS}, libs: ${CLP_LIBRARIES})")
endif(CLP_FOUND)
