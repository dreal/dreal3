cmake_minimum_required(VERSION 2.8.7)
project(DREAL CXX)
set(DREAL_VERSION_MAJOR 2)
set(DREAL_VERSION_MINOR 0)

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

# Added for CTest
INCLUDE(CTest)

set(DREAL_EXTRA_LINKER_FLAGS "")
set(DREAL_EXTRA_CXX_FLAGS "")

################################################################
# Set Module Path
################################################################
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

################################################################
# Initialize CXXFLAGS.
################################################################
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++11 ${DREAL_EXTRA_CXX_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DDREAL_DEBUG -DDREAL_TRACE -fno-inline")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

################################################################
# Compiler-specific C++11 activation.
################################################################
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
  execute_process(
    COMMAND ${CMAKE_CXX_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)
  if (NOT (GCC_VERSION VERSION_GREATER 4.8 OR GCC_VERSION VERSION_EQUAL 4.8))
    message(FATAL_ERROR "${PROJECT_NAME} requires g++ 4.8 or greater.")
  endif ()
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # In OSX, clang requires "-stdlib=libc++" to support C++11
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
    set(DREAL_EXTRA_LINKER_FLAGS "-stdlib=libc++")
  endif ()
else ()
  message(FATAL_ERROR "Your C++ compiler does not support C++11.")
endif ()

################################################################
# Fix Paths
################################################################
SET(CMAKE_SYSTEM_INCLUDE_PATH ${CMAKE_SYSTEM_INCLUDE_PATH}
  /usr/local/include /opt/local/include /usr/local/include/capd
  /usr/include/w32api
  /usr/X11R6/include /usr/include/X11
  /usr/pkg/include
  /opt/csw/include /opt/include
  /usr/include /include
  )
SET(CMAKE_SYSTEM_LIBRARY_PATH ${CMAKE_SYSTEM_LIBRARY_PATH}
  $ENV{LD_LIBRARY_PATH}
  /usr/local/lib /opt/local/lib
  /usr/lib/w32api
  /usr/X11R6/lib /usr/lib/X11
  /usr/pkg/lib
  /opt/csw/lib /opt/lib
  /usr/lib /lib
  )
SET(CMAKE_SYSTEM_PROGRAM_PATH ${CMAKE_SYSTEM_PROGRAM_PATH}
  /usr/local/bin /usr/pkg/bin /usr/bin /sbin /bin
  )
SET(CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES
  ${CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES}
  /usr/lib64 /usr/lib32 /usr/lib /lib
  )

################################################################
# Packages
################################################################
# Boost
set(Boost_USE_STATIC_LIBS        ON)
set(Boost_USE_MULTITHREADED      ON)
set(Boost_USE_STATIC_RUNTIME    OFF)
find_package(Boost 1.48.0 REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})
set(EXTRA_LIBS ${EXTRA_LIBS} ${Boost_LIBRARIES})
# Bison & Flex
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)
# CAPD
find_package(CAPD REQUIRED)
set(EXTRA_LIBS ${EXTRA_LIBS} ${CAPD_LIBRARIES})
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${CAPD_CFLAGS}")
################################################################

################################################################
# tcmalloc
################################################################
option(TCMALLOC "TCMALLOC" ON)
if("${TCMALLOC}" MATCHES "ON")
  find_package(Tcmalloc)
  if(${TCMALLOC_FOUND})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${TCMALLOC_LIBRARIES})
    message(STATUS "Using tcmalloc.")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D HAS_TCMALLOC")
  else()
    message(WARNING "FAILED to find tcmalloc, using standard malloc.")
  endif()
else()
  message(STATUS "Using standard malloc.")
endif()

################################################################
# Include Directories
################################################################
include_directories(${DREAL_SOURCE_DIR})
include_directories(${DREAL_SOURCE_DIR}/opensmt/parsers)
include_directories(${DREAL_SOURCE_DIR}/opensmt/parsers/smt2)
include_directories(${DREAL_SOURCE_DIR}/opensmt)
include_directories(${DREAL_SOURCE_DIR}/opensmt/api)
include_directories(${DREAL_SOURCE_DIR}/opensmt/cnfizers)
include_directories(${DREAL_SOURCE_DIR}/opensmt/common)
include_directories(${DREAL_SOURCE_DIR}/opensmt/egraph)
include_directories(${DREAL_SOURCE_DIR}/opensmt/minisat)
include_directories(${DREAL_SOURCE_DIR}/opensmt/minisat/core)
include_directories(${DREAL_SOURCE_DIR}/opensmt/minisat/mtl)
include_directories(${DREAL_SOURCE_DIR}/opensmt/proof)
include_directories(${DREAL_SOURCE_DIR}/opensmt/simplifiers)
include_directories(${DREAL_SOURCE_DIR}/opensmt/smtsolvers)
include_directories(${DREAL_SOURCE_DIR}/opensmt/sorts)
include_directories(${DREAL_SOURCE_DIR}/opensmt/tsolvers)
include_directories(${DREAL_SOURCE_DIR}/opensmt/tsolvers/emptysolver)
configure_file("${DREAL_SOURCE_DIR}/version.h.in" "${DREAL_BINARY_DIR}/version.h")
include_directories("${DREAL_BINARY_DIR}")

add_subdirectory(opensmt/parsers/smt2)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_smt2parser)
add_subdirectory(opensmt)
add_subdirectory(opensmt/parsers)
add_subdirectory(opensmt/egraph)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_egraph)
add_subdirectory(opensmt/common)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_common)
add_subdirectory(opensmt/api)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_api)
add_subdirectory(opensmt/cnfizers)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_cnfizers)
add_subdirectory(opensmt/sorts)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_sorts)
add_subdirectory(opensmt/minisat)
add_subdirectory(opensmt/proof)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_proof)
add_subdirectory(opensmt/simplifiers)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_simplifiers)
add_subdirectory(opensmt/smtsolvers)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_smtsolvers)
add_subdirectory(opensmt/tsolvers)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_tsolvers)
add_subdirectory(opensmt/tsolvers/emptysolver)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_emptysolver)
add_subdirectory(dsolvers)
set(DREAL_LIBS ${DREAL_LIBS} dsolvers)
add_subdirectory(realpaver)
set(DREAL_LIBS ${DREAL_LIBS} realpaver)

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread ${DREAL_EXTRA_LINKER_FLAGS} ${CAPD_LD_FLAGS}")
set(EXTRA_LIBS ${DREAL_LIBS} ${EXTRA_LIBS})
add_executable(dReal main.cpp)
target_link_libraries(dReal ${EXTRA_LIBS})
