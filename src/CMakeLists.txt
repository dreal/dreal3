cmake_minimum_required(VERSION 2.8.7)
project(DREAL CXX)
set(DREAL_VERSION_MAJOR 2)
set(DREAL_VERSION_MINOR 0)

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

# Added for CTest
#INCLUDE(CTest)

#set(DREAL_EXTRA_LINKER_FLAGS "-Wl,--rpath -Wl,LIBDIR")
set(DREAL_EXTRA_LINKER_FLAGS "")
set(DREAL_EXTRA_CXX_FLAGS "")

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++11 ${DREAL_EXTRA_CXX_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DDREAL_DEBUG -DDREAL_TRACE")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

# Compiler-specific C++11 activation.
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

# Fix Paths
SET(CMAKE_SYSTEM_INCLUDE_PATH ${CMAKE_SYSTEM_INCLUDE_PATH}
  # Locals first
  /usr/local/include /opt/local/include /usr/local/include/capd
  # Windows API on Cygwin
  /usr/include/w32api
  # X11
  /usr/X11R6/include /usr/include/X11
  # Other
  /usr/pkg/include
  /opt/csw/include /opt/include
  # Standard
  /usr/include /include
  )

SET(CMAKE_SYSTEM_LIBRARY_PATH ${CMAKE_SYSTEM_LIBRARY_PATH}
  # User environment first
  $ENV{LD_LIBRARY_PATH}
  # Locals first
  /usr/local/lib /opt/local/lib
  # Windows API on Cygwin
  /usr/lib/w32api
  # X11
  /usr/X11R6/lib /usr/lib/X11
  # Other
  /usr/pkg/lib
  /opt/csw/lib /opt/lib
  # Standard
  /usr/lib /lib
  )

SET(CMAKE_SYSTEM_PROGRAM_PATH ${CMAKE_SYSTEM_PROGRAM_PATH}
  /usr/local/bin /usr/pkg/bin /usr/bin /sbin /bin
  )

SET(CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES
  ${CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES}
  /usr/lib64 /usr/lib32 /usr/lib /lib
  )

# GMP
#find_package(GMP 5.0.5)
#set(EXTRA_LIBS ${EXTRA_LIBS} ${GMP_LIBRARIES})

# MPFR
#find_package(MPFR 3.1.0)
#set(EXTRA_LIBS ${EXTRA_LIBS} ${MPFR_LIBRARIES})

# TODO(soonhok): Find Boost
set(Boost_USE_STATIC_LIBS        ON)
set(Boost_USE_MULTITHREADED      ON)
set(Boost_USE_STATIC_RUNTIME    OFF)
find_package( Boost 1.53.0 REQUIRED)
include_directories(${Boost_INCLUDE_DIRS})
set(EXTRA_LIBS ${EXTRA_LIBS} ${Boost_LIBRARY})
message("Boost Lib=${Boost_LIBRARY}")

find_package(BISON)
find_package(FLEX)

find_package(CAPD)
set(EXTRA_LIBS ${EXTRA_LIBS} ${CAPD_LIBRARIES})
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${CAPD_CFLAGS}")

include_directories(${DREAL_SOURCE_DIR}/realpaver)
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
include_directories(${DREAL_SOURCE_DIR})
include_directories(${DREAL_SOURCE_DIR}/dsolvers)

add_subdirectory(opensmt/parsers/smt2)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_smt2parser)

add_subdirectory(opensmt)
#set(DREAL_LIBS ${DREAL_LIBS} opensmt)
add_subdirectory(opensmt/parsers)
#set(DREAL_LIBS ${DREAL_LIBS} opensmt_parsers)

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
#set(DREAL_LIBS ${DREAL_LIBS} minisat)

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

#configure_file("${LEAN_SOURCE_DIR}/shell/version.h.in" "${LEAN_BINARY_DIR}/version.h")
include_directories("${DREAL_BINARY_DIR}")
add_executable(dReal main.cpp)

target_link_libraries(dReal
${EXTRA_LIBS}
# /usr/local/lib/libcapddiffAlgebra.a
# /usr/local/lib/libcapdalglib.a
# /usr/local/lib/libcapdgeomset.a
# /usr/local/lib/libcapdintervals.a
# /usr/local/lib/libcapdauxil.a
# /usr/local/lib/libcapddynsysfacade.a
# /usr/local/lib/libcapdcovrel.a
# /usr/local/lib/libcapdalgfacade.a
# /usr/local/lib/libcapddynsys.a
# /usr/local/lib/libcapdrounding.a
# /usr/local/lib/libcapd.a
# /usr/local/lib/libcapdpoincare.a
# /usr/local/lib/libcapddiffIncl.a
# /usr/local/lib/libcapdbasicalg.a
# /usr/local/lib/libcapdmap.a
# /usr/local/lib/libcapddynset.a
# /usr/local/lib/libcapdvectalg.a
# /usr/local/lib/libcapdmatrixAlgorithms.a
# /usr/local/lib/libcapd-gui.a
)
