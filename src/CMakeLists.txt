cmake_minimum_required(VERSION 2.8.7)
project(DREAL C CXX)
set(DREAL_VERSION_MAJOR 3)
set(DREAL_VERSION_MINOR 15)
set(DREAL_VERSION_PATCH 04)
set(PACKAGE_NAME dReal)
set(PACKAGE_VERSION "${DREAL_VERSION_MAJOR}.${DREAL_VERSION_MINOR}.${DREAL_VERSION_PATCH}")
set(PACKAGE_STRING "${PACKAGE_NAME} ${PACKAGE_VERSION}")
set(PACKAGE_BUGREPORT "http://github.com/dreal/dreal/issues")
set(BUG_REPORT_URL "${PACKAGE_BUGREPORT}" CACHE STRING "Default URL where bug reports are to be submitted.")

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(SUPPORT_ODE "Support ODE" ON)
option(BUILD_STATIC_BIN  "Build static binary" OFF)
option(BUILD_SHARED_LIB "Build shared library" OFF)

# Added for CTest
include(CTest)
# Added for External Projects
include(ExternalProject)

#set(DREAL_EXTRA_LINKER_FLAGS "-D__USE_FILIB__")
#set(DREAL_EXTRA_CXX_FLAGS "-D__USE_FILIB__")
set(DREAL_EXTRA_LINKER_FLAGS "")
set(DREAL_EXTRA_CXX_FLAGS "")

################################################################
# Set Module Path
################################################################
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

################################################################
# Static Build
################################################################
if(BUILD_STATIC_BIN)
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

if(APPLE)
  set(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
  set(CMAKE_MACOSX_RPATH ON)
  set(CMAKE_INSTALL_NAME_DIR ${CMAKE_INSTALL_PREFIX}/lib)
  set(CMAKE_SKIP_BUILD_RPATH FALSE)
  set(CMAKE_BUILD_WITH_INSTALL_RPATH FALSE)
  set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")
  set(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
  list(FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES "${CMAKE_INSTALL_PREFIX}/lib" isSystemDir)
  if("${isSystemDir}" STREQUAL "-1")
    set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")
  endif()
endif()

################################################################
# Shared Lib
################################################################
if(BUILD_STATIC_BIN AND BUILD_SHARED_LIB)
  message(FATAL_ERROR "Can't handle both of BUILD_STATIC_BIN and BUILD_SHARED_LIB options." )
endif()
if(APPLE AND (${BUILD_SHARED_LIB} MATCHES "ON"))
  message(STATUS "On Mac OS X, we do not support shared library generation yet.")
  set(BUILD_SHARED_LIB "OFF")
endif()
if(BUILD_SHARED_LIB)
  set(SHARED_LIB_CONFIG_COMMAND "--enable-shared")
  set(SHARED_LIB_IBEX_COMMAND   "")
  set(SHARED_LIB_CMAKE_COMMAND  "-DBUILD_SHARED_LIBS=ON")
else()
  set(SHARED_LIB_CONFIG_COMMAND "--disable-shared")
  set(SHARED_LIB_IBEX_COMMAND   "")
  set(SHARED_LIB_CMAKE_COMMAND  "-DBUILD_SHARED_LIBS=OFF")
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
if(TESTCOV)
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
# External: FILIB
################################################################
ExternalProject_Add(FILIB
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/dreal-deps/filibxx.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND}
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make -j install
)
set(EXTRA_LIBS "prim" ${EXTRA_LIBS})

if(SUPPORT_ODE)
  ################################################################
  # External: CAPD-DynSys-4.0
  ################################################################
  ExternalProject_Add(CAPD4
    DEPENDS FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/capdDynSys-4.0.git
    GIT_TAG origin/master
    UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
    CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} --without-gui --without-boost --with-mpfr=no --with-filib=no ${SHARED_LIB_CONFIG_COMMAND}
    BUILD_COMMAND make -j
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND make -j install
    )

  ################################################################
  # External: CAPD-DynSys-3.0
  ################################################################
  # ExternalProject_Add(CAPD3
  #   PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  #   GIT_REPOSITORY https://github.com/soonhokong/capdDynSys-3.0.git
  #   GIT_TAG origin/master
  #   UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  #   CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} --without-gui --with-filib=no --with-mpfr=no
  #   BUILD_COMMAND make -j
  #   BUILD_IN_SOURCE 1
  #   INSTALL_COMMAND make -j install
  # )
  set(EXTRA_LIBS "capd" ${EXTRA_LIBS})
endif()

################################################################
# External: CLP
################################################################
ExternalProject_Add(CLP
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/dreal-deps/clp-1.16.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CC=${CMAKE_C_COMPILER} ./configure --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND} --enable-static --with-blas=BUILD --with-lapack=BUILD --disable-bzlib --disable-zlib
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)
set(EXTRA_LIBS "ClpSolver" "Clp" "CoinUtils" "m" ${EXTRA_LIBS})

################################################################
# External: ibex
################################################################
if(CMAKE_BUILD_TYPE MATCHES "DEBUG")
  set(IBEX_DEBUG_MODE "--with-debug")
endif()

ExternalProject_Add(IBEX
  DEPENDS CLP FILIB
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/dreal-deps/ibex-lib.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CC=${CMAKE_C_COMPILER} ./waf configure --prefix=${CMAKE_CURRENT_BINARY_DIR} --with-clp=${CMAKE_CURRENT_BINARY_DIR} --with-filib=${CMAKE_CURRENT_BINARY_DIR} ${IBEX_DEBUG_MODE} ${SHARED_LIB_IBEX_COMMAND}
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
  GIT_REPOSITORY https://github.com/dreal-deps/gflags.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND cmake -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER} -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER} "-DCMAKE_CXX_FLAGS=${EXTERNAL_CXX_FLAGS} -fPIC -DNDEBUG -w" ${SHARED_LIB_CMAKE_COMMAND} -DBUILD_STATIC_LIBS=ON -DCMAKE_INSTALL_PREFIX:PATH=${CMAKE_CURRENT_BINARY_DIR} ./
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
  GIT_REPOSITORY https://github.com/dreal-deps/glog.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXX_FLAGS=-DNDEBUG ${EXTERNAL_CXX_FLAGS}" CFLAGS=-DNDEBUG "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND} --with-gflags=${CMAKE_CURRENT_BINARY_DIR}
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
  GIT_REPOSITORY https://github.com/dreal-deps/googletest.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND cmake -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER} -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER} "-DCMAKE_CXX_FLAGS=${EXTERNAL_CXX_FLAGS} -w" -DCMAKE_INSTALL_PREFIX:PATH=${CMAKE_CURRENT_BINARY_DIR} ./
  BUILD_COMMAND make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND make install
)

################################################################
# External: json
################################################################
ExternalProject_Add(JSON
  PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
  GIT_REPOSITORY https://github.com/dreal-deps/json.git
  GIT_TAG origin/master
  UPDATE_COMMAND ${GIT_EXECUTABLE} pull -s recursive -X theirs origin master
  CONFIGURE_COMMAND echo "nothing to configure"
  BUILD_COMMAND CXX=${CMAKE_CXX_COMPILER} make -j
  BUILD_IN_SOURCE 1
  INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/json && cp -v src/json.hpp ${CMAKE_CURRENT_BINARY_DIR}/include/json/
)

################################################################
# Threads
################################################################
find_package (Threads REQUIRED)
set(EXTRA_LIBS ${EXTRA_LIBS} ${CMAKE_THREAD_LIBS_INIT})

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
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--rpath=${DREAL_BINARY_DIR}/lib -Wl,--no-as-needed")
endif()
if(APPLE)
  list(APPEND CMAKE_SHARED_LINKER_FLAGS "-L ${DREAL_BINARY_DIR}/lib -Xlinker -rpath -Xlinker `pwd`")
endif()

################################################################
# Include Directories
################################################################
include_directories(${DREAL_SOURCE_DIR})
include_directories(${DREAL_SOURCE_DIR}/opensmt)
configure_file("${DREAL_SOURCE_DIR}/version.h.in" "${DREAL_BINARY_DIR}/version.h")
configure_file("${DREAL_SOURCE_DIR}/config.h.in" "${DREAL_BINARY_DIR}/config.h")
include_directories("${DREAL_BINARY_DIR}")
add_subdirectory(opensmt)
################################################################
# PARSER
################################################################
# Create custom command for flex/lex (note the outputs)
ADD_CUSTOM_COMMAND(
  COMMAND ${FLEX_EXECUTABLE}
  ARGS -o ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2lexer.cc -Psmt2
  ${DREAL_SOURCE_DIR}/opensmt/parsers/smt2/smt2lexer.ll
  DEPENDS ${DREAL_SOURCE_DIR}/opensmt/parsers/smt2/smt2lexer.ll
  OUTPUT  ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2lexer.cc
  )

# Create custom command for bison/yacc (note the DEPENDS)
ADD_CUSTOM_COMMAND(
  COMMAND ${BISON_EXECUTABLE}
  ARGS -d --name-prefix=smt2 -y ${DREAL_SOURCE_DIR}/opensmt/parsers/smt2/smt2parser.yy
  -o ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2parser.cc
  DEPENDS ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2lexer.cc
  DEPENDS ${DREAL_SOURCE_DIR}/opensmt/parsers/smt2/smt2parser.yy
  OUTPUT  ${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2parser.cc
  )
# Since parser.c does not exists yet when cmake is run, mark
# it as generated
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2parser.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2lexer.cc GENERATED)
################################################################
add_subdirectory(dsolvers)
add_subdirectory(util)
add_subdirectory(contractor)

if(BUILD_SHARED_LIB)
  add_library(dreal SHARED ${DREAL_SRCS})
  if(APPLE)
    target_link_libraries(dreal ${EXTRA_LIBS})
  endif()
else()
  add_library(dreal ${DREAL_SRCS})
endif()

add_dependencies(dreal IBEX)
add_dependencies(dreal GLOG)
add_dependencies(dreal GFLAGS)
add_dependencies(dreal JSON)
if(SUPPORT_ODE)
  add_dependencies(dreal CAPD4)
endif()

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${DREAL_EXTRA_LINKER_FLAGS} ${EXTERNAL_LD_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS_TESTCOV "${CMAKE_EXE_LINKER_FLAGS} -fprofile-arcs -ftest-coverage")

add_executable(dReal-bin main.cpp)
SET_TARGET_PROPERTIES(dReal-bin
  PROPERTIES OUTPUT_NAME dReal)
target_link_libraries(dReal-bin ${EXTRA_LIBS} dreal)

#add tests
add_subdirectory(tests/util)
add_subdirectory(tests/nra)
add_subdirectory(tests/c_api)
if(SUPPORT_ODE)
  add_subdirectory(tests/capd4)
  add_subdirectory(tests/nra_ode)
endif()

# Include style check
include(StyleCheck)
file(GLOB_RECURSE DREAL_SOURCES
  ${DREAL_SOURCE_DIR}/util/*.cpp       ${DREAL_SOURCE_DIR}/util/*.h
  ${DREAL_SOURCE_DIR}/dsolvers/*.cpp   ${DREAL_SOURCE_DIR}/dsolvers/*.h
  ${DREAL_SOURCE_DIR}/tests/*.cpp      ${DREAL_SOURCE_DIR}/tests/*.h
  )
add_style_check_target(style "${DREAL_SOURCES}")
add_test(NAME style_check COMMAND ${DREAL_SOURCE_DIR}/cmake/Modules/cpplint.py "--filter=-readability/casting,-whitespace/line_length,-build/header_guard,-whitespace/indent,-runtime/references,-build/c++11" ${DREAL_SOURCES})

ADD_CUSTOM_COMMAND(TARGET dReal-bin
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

install(TARGETS dReal-bin DESTINATION bin)
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
