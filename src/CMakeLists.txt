cmake_minimum_required(VERSION 2.8.7)
project(DREAL C CXX)
set(DREAL_VERSION_MAJOR 3)
set(DREAL_VERSION_MINOR 15)
set(DREAL_VERSION_PATCH 02.1)
set(PACKAGE_NAME dReal)
set(PACKAGE_VERSION "${DREAL_VERSION_MAJOR}.${DREAL_VERSION_MINOR}.${DREAL_VERSION_PATCH}")
set(PACKAGE_STRING "${PACKAGE_NAME} ${PACKAGE_VERSION}")
set(PACKAGE_BUGREPORT "http://github.com/dreal/dreal/issues")
set(BUG_REPORT_URL "${PACKAGE_BUGREPORT}" CACHE STRING "Default URL where bug reports are to be submitted.")

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(REQUIRE_ODE "REQUIRE_ODE" OFF)
option(STATIC      "STATIC"      OFF)

# Added for CTest
include(CTest)
# Added for External Projects
include(ExternalProject)

set(DREAL_EXTRA_LINKER_FLAGS "")
set(DREAL_EXTRA_CXX_FLAGS "")

################################################################
# Set Module Path
################################################################
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

################################################################
# Static Build
################################################################
if("${STATIC}" MATCHES "ON")
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    message(STATUS "Static linking of user binaries is not supported on Mac OS X. See https://developer.apple.com/library/mac/qa/qa1118/_index.html")
    set(DREAL_EXTRA_LINKER_FLAGS "${DREAL_EXE_EXTRA_LINKER_FLAGS} -static-libgcc -static-libstdc++")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -static-libgcc -static-libstdc++")
  else()
    set(DREAL_EXTRA_LINKER_FLAGS "${DREAL_EXTRA_LINKER_FLAGS} -static -static-libgcc -static-libstdc++")
    #  set(DREAL_EXTRA_CXX_FLAGS "${DREAL_EXTRA_CXX_FLAGS} -static -static-libgcc -static-libstdc++")
    message(STATUS "Creating a static executable")
  endif()
endif()

################################################################
# Initialize CXXFLAGS.
################################################################
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++11 ${DREAL_EXTRA_CXX_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DDREAL_DEBUG -DDREAL_TRACE -fno-inline")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

################################################################
# Test coverage
################################################################
if("${TESTCOV}" MATCHES "ON")
  include(CodeCoverage)
  message(STATUS "Enable test-coverage")
  set(CMAKE_CXX_FLAGS_DEBUG        "${CMAKE_CXX_FLAGS_DEBUG} -O0 -fprofile-arcs -ftest-coverage --coverage")
  setup_target_for_coverage(cov ${DREAL_SOURCE_DIR}/script/run_tests.sh coverage)
endif()

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
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-mismatched-tags -Qunused-arguments")
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
  /usr/local/include /opt/local/include
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
# Git & Bison & Flex
find_package(GIT REQUIRED)
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

function(JOIN VALUES GLUE OUTPUT)
  string (REGEX REPLACE "([^\\]|^);" "\\1${GLUE}" _TMP_STR "${VALUES}")
  string (REGEX REPLACE "[\\](.)" "\\1" _TMP_STR "${_TMP_STR}") #fixes escaping
  set (${OUTPUT} "${_TMP_STR}" PARENT_SCOPE)
endfunction()

JOIN("${CMAKE_CXX_FLAGS}" "," EXTERNAL_CXX_FLAGS)
JOIN("${DREAL_EXTRA_LINKER_FLAGS}" "," EXTERNAL_LD_FLAGS)

################################################################
# Threads
################################################################
find_package (Threads REQUIRED)
set(EXTRA_LIBS ${CMAKE_THREAD_LIBS_INIT} ${EXTRA_LIBS})

################################################################
# External: CAPD-DynSys-4.0
################################################################
ExternalProject_Add(CAPD4
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/capdDynSys-4.0.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} --without-gui --without-boost --with-mpfr=no --with-filib=no --disable-shared
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make -j install
)
set(EXTRA_LIBS "capd" ${EXTRA_LIBS})
set(ODE_ENABLED TRUE)

################################################################
# External: FILIB
################################################################
ExternalProject_Add(FILIB
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/filibxx.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR}
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make -j install
)
set(EXTRA_LIBS "prim" ${EXTRA_LIBS})

################################################################
# External: CLP
################################################################
ExternalProject_Add(CLP
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/clp-1.16.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CC=${CMAKE_C_COMPILER} ./configure --prefix=${CMAKE_CURRENT_BINARY_DIR} --disable-shared --enable-static --with-blas=BUILD --with-lapack=BUILD --disable-bzlib --disable-zlib
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS "ClpSolver" "Clp" "CoinUtils" "m" ${EXTRA_LIBS})

################################################################
# External: ibex
################################################################
ExternalProject_Add(IBEX
  DEPENDS CLP FILIB
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/ibex-lib.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CC=${CMAKE_C_COMPILER} ./waf configure --prefix=${CMAKE_CURRENT_BINARY_DIR} --with-clp=${CMAKE_CURRENT_BINARY_DIR} --with-filib=${CMAKE_CURRENT_BINARY_DIR}
  BUILD_COMMAND ./waf build
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND ./waf install
)
set(EXTRA_LIBS "ibex" ${EXTRA_LIBS})

# Libunwind
find_package(Libunwind)
if(LIBUNWIND_FOUND)
  message(STATUS "libunwind found")
  message(STATUS "lib: ${LIBUNWIND_LIBRARY}")
  include_directories(${LIBUNWIND_INCLUDE_DIR})
  set(EXTRA_LIBS ${LIBUNWIND_LIBRARY} ${EXTRA_LIBS})
else()
  message(STATUS "libunwind not found")
endif()

################################################################
# External: gflags (Google Flags)
################################################################
ExternalProject_Add(GFLAGS
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/gflags.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND cmake -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER} "-DCMAKE_CXX_FLAGS=${EXTERNAL_CXX_FLAGS} -fPIC -DNDEBUG -w" -DCMAKE_INSTALL_PREFIX:PATH=${CMAKE_CURRENT_BINARY_DIR} ./
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS "gflags" ${EXTRA_LIBS})

################################################################
# External: glog (Google Log)
################################################################
ExternalProject_Add(GLOG
  DEPENDS GFLAGS
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/glog.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} --disable-shared "CXX_FLAGS=-DNDEBUG ${EXTERNAL_CXX_FLAGS}" CFLAGS=-DNDEBUG "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} --with-gflags=${CMAKE_CURRENT_BINARY_DIR}
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS "glog" ${EXTRA_LIBS})

################################################################
# External: googletest (Google Test)
################################################################
ExternalProject_Add(GTEST
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/googletest.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND cmake -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER} "-DCMAKE_CXX_FLAGS=${EXTERNAL_CXX_FLAGS} -w" -DCMAKE_INSTALL_PREFIX:PATH=${CMAKE_CURRENT_BINARY_DIR} ./
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS "gtest" ${EXTRA_LIBS})

################################################################
# External: json11 (Dropbox json11)
################################################################
ExternalProject_Add(JSON11
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/soonhokong/json11.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND cmake -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER} "-DCMAKE_CXX_FLAGS=${EXTERNAL_CXX_FLAGS}" "-DCMAKE_EXE_LINKER_FLAGS=${EXTERNAL_LD_FLAGS}" -DCMAKE_INSTALL_PREFIX:PATH=${CMAKE_CURRENT_BINARY_DIR} ./
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS "json11" ${EXTRA_LIBS})

################################################################
# External: set up include dir and libpath
################################################################
include_directories(${CMAKE_CURRENT_BINARY_DIR}/include)
include_directories(${CMAKE_CURRENT_BINARY_DIR}/include/ibex)
set(EXTERNAL_LD_FLAGS "-L${CMAKE_CURRENT_BINARY_DIR}/lib")

################################################################
# CXX Flags
################################################################
set(DREAL_EXTRA_CXX_FLAGS "${DREAL_EXTRA_CXX_FLAGS} -mfpmath=sse -msse -msse2 -ffloat-store")

if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  set(DREAL_EXTRA_CXX_FLAGS "${DREAL_EXTRA_CXX_FLAGS} -frounding-math")
endif()

################################################################
# EGLIBC (Optional)
################################################################
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  if("${EGLIBCPATH}" MATCHES ".+")
    message(STATUS "Use EGLIBC Installed at ${EGLIBCPATH}")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--rpath=${EGLIBCPATH}:/usr/lib/gcc/x86_64-linux-gnu/4.8:/usr/lib:/usr/lib/x86_64-linux-gnu/")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--dynamic-linker=${EGLIBCPATH}/lib/ld-linux-x86-64.so.2")
  else()
    message(STATUS "Use built-in EGLIBC.")
  endif()
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--rpath=${DREAL_BINARY_DIR}/lib")
endif()

################################################################
# Include Directories
################################################################
include_directories(${DREAL_SOURCE_DIR})
include_directories(${DREAL_SOURCE_DIR}/opensmt)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_api)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_cnfizers)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_common)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_egraph)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_emptysolver)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_simplifiers)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_smt2parser)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_smtsolvers)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_sorts)
set(DREAL_LIBS ${DREAL_LIBS} opensmt_tsolvers)
configure_file("${DREAL_SOURCE_DIR}/version.h.in" "${DREAL_BINARY_DIR}/version.h")
configure_file("${DREAL_SOURCE_DIR}/config.h.in" "${DREAL_BINARY_DIR}/config.h")
include_directories("${DREAL_BINARY_DIR}")
add_subdirectory(opensmt)
add_subdirectory(dsolvers)
set(DREAL_LIBS ${DREAL_LIBS} dsolvers)
add_subdirectory(util)
set(DREAL_LIBS ${DREAL_LIBS} util)

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${DREAL_EXTRA_LINKER_FLAGS} ${EXTERNAL_LD_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS_TESTCOV "${CMAKE_EXE_LINKER_FLAGS} -fprofile-arcs -ftest-coverage")

add_executable(dReal main.cpp)
target_link_libraries(dReal ${DREAL_LIBS} ${EXTRA_LIBS})

#add tests
add_subdirectory(tests/util)
add_subdirectory(tests/nra)
add_subdirectory(tests/nra_ode)
add_subdirectory(tests/c_api)
add_subdirectory(tests/capd4)

# Include style check
include(StyleCheck)
file(GLOB_RECURSE DREAL_SOURCES
  ${DREAL_SOURCE_DIR}/util/*.cpp       ${DREAL_SOURCE_DIR}/util/*.h
  ${DREAL_SOURCE_DIR}/dsolvers/*.cpp   ${DREAL_SOURCE_DIR}/dsolvers/*.h
  ${DREAL_SOURCE_DIR}/tests/*.cpp      ${DREAL_SOURCE_DIR}/tests/*.h
  )
add_style_check_target(style "${DREAL_SOURCES}")
add_test(NAME style_check COMMAND ${DREAL_SOURCE_DIR}/cmake/Modules/cpplint.py "--filter=-readability/casting,-whitespace/line_length,-build/header_guard,-whitespace/indent,-runtime/references,-build/c++11" ${DREAL_SOURCES})

ADD_CUSTOM_COMMAND(TARGET dReal
          POST_BUILD
          COMMAND ${CMAKE_COMMAND} -E make_directory ${DREAL_SOURCE_DIR}/../bin
          COMMAND ${CMAKE_COMMAND} -E copy ${DREAL_BINARY_DIR}/dReal ${DREAL_SOURCE_DIR}/../bin/
)

#########################################
# CPack
#########################################
set(CPACK_PACKAGE_NAME dReal)
string(TOLOWER ${CMAKE_SYSTEM_NAME} LOWER_SYSTEM_NAME)
set(CPACK_PACKAGE_FILE_NAME "dReal-${DREAL_VERSION_MAJOR}.${DREAL_VERSION_MINOR}.${DREAL_VERSION_PATCH}-${LOWER_SYSTEM_NAME}")
set(CPACK_STRIP_FILES TRUE)
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  SET(CPACK_GENERATOR TGZ)
else()
  SET(CPACK_GENERATOR ZIP)
endif()
include(CPack)

install(TARGETS dReal DESTINATION bin)
install(FILES ${DREAL_SOURCE_DIR}/../bin/dReach DESTINATION bin
  PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE
              GROUP_READ GROUP_WRITE GROUP_EXECUTE
              WORLD_READ WORLD_EXECUTE)
set(BMC_PATH ${DREAL_SOURCE_DIR}/../tools/_build/bmc/src/bmc_main.native)
if(EXISTS ${BMC_PATH})
  message(STATUS "found bmc")
  install(FILES ${BMC_PATH} DESTINATION bin
    PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE
                GROUP_READ GROUP_WRITE GROUP_EXECUTE
                WORLD_READ WORLD_EXECUTE)
endif()
