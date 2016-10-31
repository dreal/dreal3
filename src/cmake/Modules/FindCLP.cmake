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
if(BZip2_FOUND)
    if(APPLE)
        if(EXISTS /usr/local/include/clp)
            pkg_check_modules(CLP clp)
            list(APPEND CLP_INCLUDE_DIRS /usr/local/include/clp)
        endif()
    else(APPLE)
        pkg_check_modules(CLP clp)
    endif(APPLE)
else(BZip2_Found)
    message(STATUS "Failed to find bzip2 which is required for CLP.")
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        message(STATUS "Please install 'libbz2-dev' package.")
    endif()
endif(BZip2_FOUND)

if(CLP_FOUND)
    message(STATUS "Clp found (includes: ${CLP_INCLUDE_DIRS}, libs: ${CLP_LIBRARIES})")
else(CLP_FOUND)
    message(STATUS "Failed to find CLP. --polytope option is disabled as a result.")
    if(APPLE)
        message(STATUS "Please install CLP via 'brew install coin-or-tools/coinor/clp'.")
    endif(APPLE)
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        message(STATUS "Please install CLP via 'sudo apt-get install coinor-libclp-dev'.")
    endif()
endif(CLP_FOUND)
