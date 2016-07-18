cmake_minimum_required(VERSION 2.8.12)
project(DREAL C CXX)
set(DREAL_VERSION_MAJOR 3)
set(DREAL_VERSION_MINOR 16)
set(DREAL_VERSION_PATCH 07)
set(PACKAGE_NAME dReal)
set(PACKAGE_VERSION "${DREAL_VERSION_MAJOR}.${DREAL_VERSION_MINOR}.${DREAL_VERSION_PATCH}")
set(PACKAGE_STRING "${PACKAGE_NAME} ${PACKAGE_VERSION}")
set(PACKAGE_BUGREPORT "http://github.com/dreal/dreal3/issues")
set(BUG_REPORT_URL "${PACKAGE_BUGREPORT}" CACHE STRING "Default URL where bug reports are to be submitted.")

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(SUPPORT_ODE      "Support ODE" ON)
option(LOGGING          "Enable Logging" ON)
option(BUILD_STATIC_BIN "Build static binary"  OFF)
option(BUILD_SHARED_LIB "Build shared library" OFF)
option(USE_LOCAL_THIRD_PARTY "Use local third party libraries" OFF)
option(USE_GLPK         "Use local third party libraries" OFF)
option(TCMALLOC         "Use tcmalloc (a.k.a. gperftools)" ON)
option(BUILD_TEST       "Build test binaries" ON)
option(USE_ASAN         "Use address sanitizer (-fsanitize=address)" OFF)

# Added for CTest
include(CTest)
# Added for External Projects
include(ExternalProject)

################################################################
# CXX Flags
################################################################
set(DREAL_EXTRA_CXX_FLAGS "${DREAL_EXTRA_CXX_FLAGS} -mfpmath=sse -msse -msse2")
if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
  set(DREAL_EXTRA_CXX_FLAGS "${DREAL_EXTRA_CXX_FLAGS} -ffloat-store -frounding-math")
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  message(WARNING "Clang does not support -ffloat-store and -frounding-math options "
    "which are required to guarantee the correctness of the interval arithmetic.")
else()
  message(WARNING "We added compiler flags -ffloat-store and -frounding-math, "
    "but it is possible that your compiler do not support the options. "
    "If that is the case, please contact Soonho Kong <soonhok@cs.cmu.edu>.")
  set(DREAL_EXTRA_CXX_FLAGS "${DREAL_EXTRA_CXX_FLAGS} -ffloat-store -frounding-math")
endif()

################################################################
# Initialize CXXFLAGS.
################################################################
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++11 ${DREAL_EXTRA_CXX_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DDREAL_DEBUG -DDREAL_TRACE -fno-inline")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

if(USE_ASAN)
  message(STATUS "Using address sanitizer (-fsanitizer=address)")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address -fno-omit-frame-pointer")
  if(${CMAKE_CXX_COMPILER_ID} MATCHES "GNU")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fuse-ld=gold")
    set(EXTRA_LIBS "asan" ${EXTRA_LIBS})
  endif()
endif(USE_ASAN)

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
    if("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
      set(DREAL_EXTRA_LINKER_FLAGS "${DREAL_EXTRA_LINKER_FLAGS} ${DREAL_EXE_EXTRA_LINKER_FLAGS} -static-libgcc -static-libstdc++")
      # set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -static-libgcc -static-libstdc++")
    endif()
    if("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
      set(DREAL_EXTRA_LINKER_FLAGS "${DREAL_EXTRA_LINKER_FLAGS} ${DREAL_EXE_EXTRA_LINKER_FLAGS} -static-libstdc++")
      set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -static-libstdc++ ")
    endif()
  else()
    set(DREAL_EXTRA_LINKER_FLAGS "${DREAL_EXTRA_LINKER_FLAGS} ${DREAL_EXTRA_LINKER_FLAGS} -static -static-libgcc -static-libstdc++")
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
if(APPLE AND BUILD_SHARED_LIB)
  message(STATUS "OSX + BUILD_SHARED_LIB: Run target 'shared_lib' to generate lib/libdreal.dylib")
endif()
if((NOT APPLE) AND BUILD_SHARED_LIB)
  set(SHARED_LIB_CONFIG_COMMAND "--enable-shared")
  set(SHARED_LIB_IBEX_COMMAND   "--enable-shared")
  set(SHARED_LIB_CMAKE_COMMAND  "-DBUILD_SHARED_LIBS=ON")
else()
  # In case of APPLE, we still only generate static libraries (.a). We
  # will later convert them to a single dylib file.
  set(SHARED_LIB_CONFIG_COMMAND "--disable-shared")
  set(SHARED_LIB_IBEX_COMMAND   "")
  set(SHARED_LIB_CMAKE_COMMAND  "-DBUILD_SHARED_LIBS=OFF")
endif()

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
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # In OSX, clang requires "-stdlib=libc++" to support C++11
    MESSAGE("In OSX, clang requires -stdlib=libc++ to support C++11")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
    set(DREAL_EXTRA_LINKER_FLAGS "${DREAL_EXTRA_LINKER_FLAGS} -stdlib=libc++")
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
# tcmalloc
################################################################
if(NOT "${JEMALLOC_FOUND}")
  if(NOT BUILD_STATIC_BIN AND TCMALLOC)
    find_package(Tcmalloc)
    if(${TCMALLOC_FOUND})
      set(EXTRA_LIBS ${EXTRA_LIBS} ${TCMALLOC_LIBRARIES})
      message(STATUS "Using tcmalloc.")
      set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D HAS_TCMALLOC")
    else()
      message(STATUS "Failed to find tcmalloc, using standard malloc.")
    endif()
  else()
    message(STATUS "Using standard malloc.")
  endif()
endif()

################################################################
# Packages
################################################################
# Git & Bison & Flex
find_package(GIT REQUIRED)
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

# FindPythonLibs
set(Python_ADDITIONAL_VERSIONS 2.7)
find_package(PythonInterp REQUIRED)
find_package(PythonLibs 2.7)
if(PYTHONLIBS_FOUND)
  include_directories("${PYTHON_INCLUDE_DIR}")
endif()

function(JOIN VALUES GLUE OUTPUT)
  string (REGEX REPLACE "([^\\]|^);" "\\1${GLUE}" _TMP_STR "${VALUES}")
  string (REGEX REPLACE "[\\](.)" "\\1" _TMP_STR "${_TMP_STR}") #fixes escaping
  set (${OUTPUT} "${_TMP_STR}" PARENT_SCOPE)
endfunction()

JOIN("${CMAKE_CXX_FLAGS}" "," EXTERNAL_CXX_FLAGS)
JOIN("${DREAL_EXTRA_LINKER_FLAGS}" "," EXTERNAL_LD_FLAGS)

################################################################
# External: PICOSAT
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(PICOSAT
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/picosat.zip
    CONFIGURE_COMMAND CC=${CMAKE_C_COMPILER} ./configure.sh # ${SHARED_LIB_CONFIG_COMMAND} # --prefix=${CMAKE_CURRENT_BINARY_DIR}
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/picosat && cp picosat.h ${CMAKE_CURRENT_BINARY_DIR}/include/picosat && cp libpicosat.a ${CMAKE_CURRENT_BINARY_DIR}/lib)
else()
  ExternalProject_Add(PICOSAT
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/picosat.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
    COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND CC=${CMAKE_C_COMPILER} ./configure.sh # --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND}
    BUILD_COMMAND CC=${CMAKE_C_COMPILER} make VERBOSE=1
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/picosat && cp picosat.h ${CMAKE_CURRENT_BINARY_DIR}/include/picosat && cp libpicosat.a ${CMAKE_CURRENT_BINARY_DIR}/lib )
endif()
set(EXTRA_LIBS "picosat" ${EXTRA_LIBS})

################################################################
# External: FILIB
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/filibxx.zip
    CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND}
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND make install)
else()
  ExternalProject_Add(FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/filibxx.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
    COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND}
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND make install)
endif()
set(EXTRA_LIBS "prim" ${EXTRA_LIBS})

################################################################
# External: GLPK
################################################################
if(USE_GLPK)
  if(USE_LOCAL_THIRD_PARTY)
    ExternalProject_Add(GLPK
      PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
      URL ${CMAKE_SOURCE_DIR}/third_party/glpk.zip
      CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND}
      BUILD_COMMAND make
      BUILD_IN_SOURCE 1
      INSTALL_COMMAND make install)
  else()
    ExternalProject_Add(GLPK
      PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
      GIT_REPOSITORY https://github.com/dreal-deps/glpk.git
      GIT_TAG master
      UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
      COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
      CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND}
      BUILD_COMMAND make
      BUILD_IN_SOURCE 1
      INSTALL_COMMAND make install)
  endif()
  set(EXTRA_LIBS "glpk" ${EXTRA_LIBS})
endif()

################################################################
# External: NLOPT
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(NLOPT
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/nlopt.zip
    CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -Wno-deprecated-declarations -w" CFLAGS=-Wno-deprecated-declarations "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND} --without-guile --without-python --without-octave --without-matlab
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND make install)
else()
  ExternalProject_Add(NLOPT
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/nlopt.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
    COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -Wno-deprecated-declarations -w" CFLAGS=-Wno-deprecated-declarations "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND} --without-guile --without-python --without-octave --without-matlab
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND make install)
endif()
set(EXTRA_LIBS "nlopt" ${EXTRA_LIBS})

if(SUPPORT_ODE)
  ################################################################
  # External: CAPD-DynSys-4.0
  ################################################################
  if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(CAPD4
    DEPENDS FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/capdDynSys-4.0.zip
    CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} --without-gui --without-boost --with-mpfr=no --with-filib=no ${SHARED_LIB_CONFIG_COMMAND}
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND make install)
  else()
    ExternalProject_Add(CAPD4
      DEPENDS FILIB
      PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
      GIT_REPOSITORY https://github.com/dreal-deps/capdDynSys-4.0.git
      GIT_TAG master
      UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
      COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
      CONFIGURE_COMMAND autoreconf --install > /dev/null 2>&1 || autoreconf && ./configure CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER} "CXXFLAGS=${EXTERNAL_CXX_FLAGS} -w" "LDFLAGS=${EXTERNAL_LD_FLAGS}" --prefix=${CMAKE_CURRENT_BINARY_DIR} --without-gui --without-boost --with-mpfr=no --with-filib=no ${SHARED_LIB_CONFIG_COMMAND}
      BUILD_COMMAND make
      BUILD_IN_SOURCE 1
      INSTALL_COMMAND make install)
  endif()
  set(EXTRA_LIBS "capd" ${EXTRA_LIBS})
endif()

################################################################
# External: CLP
################################################################
if(MINGW)
  ExternalProject_Add(CLP
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/clp-1.16.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
           COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CXXFLAGS=--std=c++11 CC=${CMAKE_C_COMPILER} ./configure --build=x86_64-w64-mingw32 --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND} --enable-static --with-blas=BUILD --with-lapack=BUILD --disable-bzlib --disable-zlib
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/coin && mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/share/coin/doc/CoinUtils && make install)
else(MINGW)
  if(USE_LOCAL_THIRD_PARTY)
    ExternalProject_Add(CLP
      PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
      URL ${CMAKE_SOURCE_DIR}/third_party/clp-1.16.zip
      CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CXXFLAGS=--std=c++11 CC=${CMAKE_C_COMPILER} ./configure --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND} --enable-static --with-blas=BUILD --with-lapack=BUILD --disable-bzlib --disable-zlib
      BUILD_COMMAND make
      BUILD_IN_SOURCE 1
      INSTALL_COMMAND make install)
  else(USE_LOCAL_THIRD_PARTY)
    ExternalProject_Add(CLP
      PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
      GIT_REPOSITORY https://github.com/dreal-deps/clp-1.16.git
      GIT_TAG master
      UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
      COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
      CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CXXFLAGS=--std=c++11 CC=${CMAKE_C_COMPILER} ./configure --prefix=${CMAKE_CURRENT_BINARY_DIR} ${SHARED_LIB_CONFIG_COMMAND} --enable-static --with-blas=BUILD --with-lapack=BUILD --disable-bzlib --disable-zlib
      BUILD_COMMAND make
      BUILD_IN_SOURCE 1
      INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/coin && mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/share/coin/doc/CoinUtils && make install)
  endif()
endif()
set(EXTRA_LIBS "ClpSolver" "Clp" "CoinUtils" ${EXTRA_LIBS})

################################################################
# External: ibex
################################################################
if(CMAKE_BUILD_TYPE MATCHES "DEBUG")
  set(IBEX_DEBUG_MODE "--with-debug")
endif()

if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(IBEX
    DEPENDS CLP FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/ibex-lib.zip
    CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CXXFLAGS=--std=c++11 CC=${CMAKE_C_COMPILER} ./waf configure --with-optim --prefix=${CMAKE_CURRENT_BINARY_DIR} --with-clp=${CMAKE_CURRENT_BINARY_DIR} --with-filib=${CMAKE_CURRENT_BINARY_DIR} ${IBEX_DEBUG_MODE} ${SHARED_LIB_IBEX_COMMAND}
    BUILD_COMMAND ./waf build
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND ./waf install)
else()
  ExternalProject_Add(IBEX
    DEPENDS CLP FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/ibex-lib.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
    COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND CXX=${CMAKE_CXX_COMPILER} CXXFLAGS=--std=c++11 CC=${CMAKE_C_COMPILER} ./waf configure --with-optim --prefix=${CMAKE_CURRENT_BINARY_DIR} --with-clp=${CMAKE_CURRENT_BINARY_DIR} --with-filib=${CMAKE_CURRENT_BINARY_DIR} ${IBEX_DEBUG_MODE} ${SHARED_LIB_IBEX_COMMAND}
    BUILD_COMMAND ./waf build
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND ./waf install)
endif()
set(EXTRA_LIBS "ibex" ${EXTRA_LIBS})

################################################################
# External: Catch (testing framework)
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(CATCH
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/Catch.zip
    CONFIGURE_COMMAND echo "nothing to configure"
    BUILD_COMMAND echo "nothing to build"
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/catch && cp -v single_include/catch.hpp ${CMAKE_CURRENT_BINARY_DIR}/include/catch/)
else(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(CATCH
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/Catch.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
    COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND echo "nothing to configure"
    BUILD_COMMAND echo "nothing to build"
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/catch && cp -v single_include/catch.hpp ${CMAKE_CURRENT_BINARY_DIR}/include/catch/)
endif()
################################################################
# External: Easylogging++
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(EASYLOGGINGPP
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/easyloggingpp.zip
    CONFIGURE_COMMAND echo "nothing to configure"
    BUILD_COMMAND echo "nothing to build"
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/easylogingpp && cp -v src/easylogging++.h ${CMAKE_CURRENT_BINARY_DIR}/include/easylogingpp/)
else()
  ExternalProject_Add(EASYLOGGINGPP
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/easyloggingpp.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
    COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND echo "nothing to configure"
    BUILD_COMMAND echo "nothing to build"
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/easylogingpp && cp -v src/easylogging++.h ${CMAKE_CURRENT_BINARY_DIR}/include/easylogingpp/)
endif()
################################################################
# External: ezoptionparser
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(EZOPTIONPARSER
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/ezoptionparser.zip
    CONFIGURE_COMMAND echo "nothing to configure"
    BUILD_COMMAND echo "nothing to build"
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/ezOptionParser/ && make PREFIX=${CMAKE_CURRENT_BINARY_DIR} install)
else()
  ExternalProject_Add(EZOPTIONPARSER
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/ezoptionparser.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
    COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND echo "nothing to configure"
    BUILD_COMMAND echo "nothing to build"
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/ezOptionParser/ && make PREFIX=${CMAKE_CURRENT_BINARY_DIR} install)
endif()
################################################################
# External: json
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(JSON
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/json.zip
    CONFIGURE_COMMAND echo "nothing to configure"
    BUILD_COMMAND echo "nothing to build"
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/json && cp -v src/json.hpp ${CMAKE_CURRENT_BINARY_DIR}/include/json/)
else()
  ExternalProject_Add(JSON
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/json.git
    GIT_TAG master
    UPDATE_COMMAND ${GIT_EXECUTABLE} fetch --all
    COMMAND ${GIT_EXECUTABLE} reset --hard origin/master
    CONFIGURE_COMMAND echo "nothing to configure"
    BUILD_COMMAND echo "nothing to build"
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/json && cp -v src/json.hpp ${CMAKE_CURRENT_BINARY_DIR}/include/json/)
endif()
################################################################
# Threads
################################################################
find_package (Threads REQUIRED)
set(EXTRA_LIBS ${EXTRA_LIBS} ${CMAKE_THREAD_LIBS_INIT})

################################################################
# LIBM - math
################################################################
set(EXTRA_LIBS ${EXTRA_LIBS} "m")

################################################################
# External: set up include dir and libpath
################################################################
include_directories(${CMAKE_CURRENT_BINARY_DIR}/include)
include_directories(${CMAKE_CURRENT_BINARY_DIR}/include/ibex)
set(EXTERNAL_LD_FLAGS "-L${CMAKE_CURRENT_BINARY_DIR}/lib")

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
# PARSER: SMT2
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
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/smt2/smt2lexer.cc PROPERTIES COMPILE_FLAGS -Wno-sign-compare)
################################################################
# PARSER: DR
################################################################
# Create custom command for flex/lex (note the outputs)
ADD_CUSTOM_COMMAND(
  COMMAND ${FLEX_EXECUTABLE}
  ARGS -o ${DREAL_BINARY_DIR}/opensmt/parsers/dr/drlexer.cc -Pdr
  ${DREAL_SOURCE_DIR}/opensmt/parsers/dr/drlexer.ll
  DEPENDS ${DREAL_SOURCE_DIR}/opensmt/parsers/dr/drlexer.ll
  OUTPUT  ${DREAL_BINARY_DIR}/opensmt/parsers/dr/drlexer.cc
  )

# Create custom command for bison/yacc (note the DEPENDS)
ADD_CUSTOM_COMMAND(
  COMMAND ${BISON_EXECUTABLE}
  ARGS -d --name-prefix=dr -y ${DREAL_SOURCE_DIR}/opensmt/parsers/dr/drparser.yy
  -o ${DREAL_BINARY_DIR}/opensmt/parsers/dr/drparser.cc
  DEPENDS ${DREAL_BINARY_DIR}/opensmt/parsers/dr/drlexer.cc
  DEPENDS ${DREAL_SOURCE_DIR}/opensmt/parsers/dr/drparser.yy
  OUTPUT  ${DREAL_BINARY_DIR}/opensmt/parsers/dr/drparser.cc
  )
# Since parser.c does not exists yet when cmake is run, mark
# it as generated
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/dr/drparser.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/dr/drlexer.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/dr/drlexer.cc PROPERTIES COMPILE_FLAGS -Wno-sign-compare)
################################################################
# PARSER: DOP
################################################################
# Create custom command for flex/lex (note the outputs)
ADD_CUSTOM_COMMAND(
  COMMAND ${FLEX_EXECUTABLE}
  ARGS -o ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc -Pdop
  ${DREAL_SOURCE_DIR}/tools/dop/parsers/dop/doplexer.ll
  DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/dop/doplexer.ll
  OUTPUT  ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc
  )

# Create custom command for bison/yacc (note the DEPENDS)
ADD_CUSTOM_COMMAND(
  COMMAND ${BISON_EXECUTABLE}
  ARGS -d --name-prefix=dop -y ${DREAL_SOURCE_DIR}/tools/dop/parsers/dop/dopparser.yy
  -o ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/dopparser.cc
  DEPENDS ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc
  DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/dop/dopparser.yy
  OUTPUT  ${DREAL_BINARY_DIR}/tools/dop/parsers/dop/dopparser.cc
  )
# Since parser.c does not exists yet when cmake is run, mark
# it as generated
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/dop/dopparser.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/dop/doplexer.cc PROPERTIES COMPILE_FLAGS -Wno-sign-compare)
################################################################
# PARSER: BARON
################################################################
# Create custom command for flex/lex (note the outputs)
ADD_CUSTOM_COMMAND(
  COMMAND ${FLEX_EXECUTABLE}
  ARGS -o ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc -Pbaron
  ${DREAL_SOURCE_DIR}/tools/dop/parsers/baron/baronlexer.ll
  DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/baron/baronlexer.ll
  OUTPUT  ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc
  )

# Create custom command for bison/yacc (note the DEPENDS)
ADD_CUSTOM_COMMAND(
  COMMAND ${BISON_EXECUTABLE}
  ARGS -d --name-prefix=baron -y ${DREAL_SOURCE_DIR}/tools/dop/parsers/baron/baronparser.yy
  -o ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc
  DEPENDS ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc
  DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/baron/baronparser.yy
  OUTPUT  ${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc
  )
# Since parser.c does not exists yet when cmake is run, mark
# it as generated
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronparser.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/baron/baronlexer.cc PROPERTIES COMPILE_FLAGS -Wno-sign-compare)
################################################################
# PARSER: BCH
################################################################
# Create custom command for flex/lex (note the outputs)
ADD_CUSTOM_COMMAND(
  COMMAND ${FLEX_EXECUTABLE}
  ARGS -o ${DREAL_BINARY_DIR}/tools/dop/parsers/bch/bchlexer.cc -Pbch
  ${DREAL_SOURCE_DIR}/tools/dop/parsers/bch/bchlexer.ll
  DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/bch/bchlexer.ll
  OUTPUT  ${DREAL_BINARY_DIR}/tools/dop/parsers/bch/bchlexer.cc
  )

# Create custom command for bison/yacc (note the DEPENDS)
ADD_CUSTOM_COMMAND(
  COMMAND ${BISON_EXECUTABLE}
  ARGS -d --name-prefix=bch -y ${DREAL_SOURCE_DIR}/tools/dop/parsers/bch/bchparser.yy
  -o ${DREAL_BINARY_DIR}/tools/dop/parsers/bch/bchparser.cc
  DEPENDS ${DREAL_BINARY_DIR}/tools/dop/parsers/bch/bchlexer.cc
  DEPENDS ${DREAL_SOURCE_DIR}/tools/dop/parsers/bch/bchparser.yy
  OUTPUT  ${DREAL_BINARY_DIR}/tools/dop/parsers/bch/bchparser.cc
  )
# Since parser.c does not exists yet when cmake is run, mark
# it as generated
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/bch/bchparser.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/bch/bchlexer.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/tools/dop/parsers/bch/bchlexer.cc PROPERTIES COMPILE_FLAGS -Wno-sign-compare)
################################################################
add_subdirectory(icp)
add_subdirectory(dsolvers)
add_subdirectory(util)
add_subdirectory(constraint)
add_subdirectory(contractor)
add_subdirectory(tools/dop)
add_subdirectory(api)
add_subdirectory(optimizer)

SET(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${DREAL_BINARY_DIR}/lib")
SET(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${DREAL_BINARY_DIR}/lib")
if((NOT APPLE) AND BUILD_SHARED_LIB)
  add_library(dreal SHARED ${DREAL_SRCS})
  add_library(dop SHARED ${DOP_SRCS})
else()
  add_library(dreal ${DREAL_SRCS})
  add_library(dop ${DOP_SRCS})
endif()

add_dependencies(dop PICOSAT)
add_dependencies(dop IBEX)
add_dependencies(dop NLOPT)
add_dependencies(dop EASYLOGGINGPP)
add_dependencies(dop EZOPTIONPARSER)
add_dependencies(dop JSON)
add_dependencies(dreal PICOSAT)
add_dependencies(dreal IBEX)
add_dependencies(dreal NLOPT)
add_dependencies(dreal EASYLOGGINGPP)
add_dependencies(dreal EZOPTIONPARSER)
add_dependencies(dreal JSON)
if(USE_GLPK)
  add_dependencies(dreal GLPK)
  add_dependencies(dop GLPK)
endif()
if(SUPPORT_ODE)
  add_dependencies(dreal CAPD4)
  add_dependencies(dop CAPD4)
endif()

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${DREAL_EXTRA_LINKER_FLAGS} ${EXTERNAL_LD_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS_TESTCOV "${CMAKE_EXE_LINKER_FLAGS} -fprofile-arcs -ftest-coverage")

add_executable(dReal-bin main.cpp)
SET_TARGET_PROPERTIES(dReal-bin
  PROPERTIES OUTPUT_NAME dReal)
target_link_libraries(dReal-bin dreal ${EXTRA_LIBS})

# Compatibility Checks using https://github.com/foonathan/compatibility
include(CompBase)
comp_target_features(dReal-bin PUBLIC CPP11)
configure_file("${DREAL_SOURCE_DIR}/compatibility.h.in" "${DREAL_BINARY_DIR}/compatibility.h")

if(NOT BUILD_STATIC_BIN)
  add_executable(dOp-bin tools/dop/main.cpp)
  SET_TARGET_PROPERTIES(dOp-bin PROPERTIES OUTPUT_NAME dOp)
  if(${PYTHONLIBS_FOUND})
    target_link_libraries(dOp-bin dop dreal ${PYTHON_LIBRARIES} ${EXTRA_LIBS})
  else()
    target_link_libraries(dOp-bin dop dreal ${EXTRA_LIBS})
  endif()
endif()

#add tests
if(BUILD_TEST)
  add_subdirectory(tests/util)
  add_subdirectory(tests/nra)
  add_subdirectory(tests/c_api)
  add_subdirectory(tests/cpp_api)
  add_subdirectory(tests/ibex)
  add_subdirectory(tests/nlopt)
  if(USE_GLPK)
    add_subdirectory(tests/glpk)
  endif()
  add_subdirectory(tests/contractor)
  if(SUPPORT_ODE)
    add_subdirectory(tests/capd4)
    add_subdirectory(tests/nra_ode)
    add_subdirectory(tests/drh)
  endif()
endif()

if(WITH_COLIN)
add_dependencies(dReal colin_copy)
add_dependencies(dReal val_copy)
endif(WITH_COLIN)

# Include style check
include(StyleCheck)
file(GLOB_RECURSE DREAL_SOURCES
  ${DREAL_SOURCE_DIR}/api/*.h          ${DREAL_SOURCE_DIR}/api/*.hh
  ${DREAL_SOURCE_DIR}/api/*.C          ${DREAL_SOURCE_DIR}/api/*.cpp
  ${DREAL_SOURCE_DIR}/contractor/*.cpp ${DREAL_SOURCE_DIR}/contractor/*.h
  ${DREAL_SOURCE_DIR}/constraint/*.cpp ${DREAL_SOURCE_DIR}/constraint/*.h
  ${DREAL_SOURCE_DIR}/util/*.cpp       ${DREAL_SOURCE_DIR}/util/*.h
  ${DREAL_SOURCE_DIR}/icp/*.cpp        ${DREAL_SOURCE_DIR}/icp/*.h
  ${DREAL_SOURCE_DIR}/dsolvers/*.cpp   ${DREAL_SOURCE_DIR}/dsolvers/*.h
  ${DREAL_SOURCE_DIR}/optimizer/*.cpp   ${DREAL_SOURCE_DIR}/optimizer/*.h
  ${DREAL_SOURCE_DIR}/tests/*.cpp      ${DREAL_SOURCE_DIR}/tests/*.h
  ${DREAL_SOURCE_DIR}/tools/dop/*.cpp  ${DREAL_SOURCE_DIR}/tools/dop/*.h)
add_style_check_target(style "${DREAL_SOURCES}")
add_test(NAME style_check COMMAND ${DREAL_SOURCE_DIR}/cmake/Modules/cpplint.py "--filter=-readability/casting,-whitespace/line_length,-build/header_guard,-whitespace/indent,-runtime/references,-build/c++11,-runtime/int" ${DREAL_SOURCES})

ADD_CUSTOM_COMMAND(TARGET dReal-bin
          POST_BUILD
          COMMAND ${CMAKE_COMMAND} -E make_directory ${DREAL_SOURCE_DIR}/../bin
          COMMAND ${CMAKE_COMMAND} -E copy ${DREAL_BINARY_DIR}/dReal ${DREAL_SOURCE_DIR}/../bin/
)
if(NOT BUILD_STATIC_BIN)
  ADD_CUSTOM_COMMAND(TARGET dOp-bin
            POST_BUILD
            COMMAND ${CMAKE_COMMAND} -E make_directory ${DREAL_SOURCE_DIR}/../bin
            COMMAND ${CMAKE_COMMAND} -E copy ${DREAL_BINARY_DIR}/dOp ${DREAL_SOURCE_DIR}/../bin/
  )
endif()

#########################################
# CPack
#########################################
set(CPACK_PACKAGE_NAME dReal)
string(TOLOWER ${CMAKE_SYSTEM_NAME} LOWER_SYSTEM_NAME)
if(BUILD_SHARED_LIB)
  set(CPACK_PACKAGE_FILE_NAME "dReal-${DREAL_VERSION_MAJOR}.${DREAL_VERSION_MINOR}.${DREAL_VERSION_PATCH}-${LOWER_SYSTEM_NAME}-shared-libs")
else()
  set(CPACK_PACKAGE_FILE_NAME "dReal-${DREAL_VERSION_MAJOR}.${DREAL_VERSION_MINOR}.${DREAL_VERSION_PATCH}-${LOWER_SYSTEM_NAME}")
endif()
set(CPACK_STRIP_FILES TRUE)
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  SET(CPACK_GENERATOR TGZ)
else()
  SET(CPACK_GENERATOR ZIP)
endif()
include(CPack)

########################################
# INSTALL
########################################
install(DIRECTORY "${DREAL_BINARY_DIR}/lib" DESTINATION "./"
  FILES_MATCHING
  PATTERN "*.a"
  PATTERN "*.la"
  PATTERN "*.so"
  PATTERN "*.dylib")

install(DIRECTORY "${DREAL_BINARY_DIR}/include" DESTINATION "./"
  FILES_MATCHING
  PATTERN "*.cpp"
  PATTERN "*.f"
  PATTERN "*.h"
  PATTERN "*.h_"
  PATTERN "*.hpp"
  PATTERN "*.icc")

install(TARGETS dReal-bin DESTINATION bin)
if(NOT BUILD_STATIC_BIN)
  install(TARGETS dOp-bin DESTINATION bin)
endif()
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
if(BUILD_SHARED_LIB)
  install(DIRECTORY "${DREAL_BINARY_DIR}/lib"
          DESTINATION ".")
  install(FILES "${DREAL_SOURCE_DIR}/opensmt/api/opensmt_c.h"
          DESTINATION "include")
endif()

if(APPLE AND BUILD_SHARED_LIB)
  if (USE_GLPK)
    add_custom_target(shared_lib
      COMMAND echo "Building Shared Library..."
      COMMAND cd lib && ${CMAKE_CXX_COMPILER} -fpic -shared -Wl,-all_load libdreal.a libcapd.a libibex.a libnlopt.a libprim.a libClp.a libClpSolver.a libCoinUtils.a libglpk.a -o libdreal.dylib
      DEPENDS dreal CAPD4 IBEX FILIB CLP NLOPT GLPK PICOSAT)
  else()
    add_custom_target(shared_lib
      COMMAND echo "Building Shared Library..."
      COMMAND cd lib && ${CMAKE_CXX_COMPILER} -fpic -shared -Wl,-all_load libdreal.a libcapd.a libibex.a libnlopt.a libprim.a libClp.a libClpSolver.a libCoinUtils.a -o libdreal.dylib
      DEPENDS dreal CAPD4 IBEX FILIB CLP NLOPT PICOSAT)
  endif()
endif()

add_custom_target(update_pkgs
  COMMAND echo "Update External Packages"
  COMMAND ${CMAKE_BUILD_TOOL})

if(USE_GLPK)
  add_custom_target(update_glpk
    COMMAND git fetch --all && git reset --hard origin/master && make install
    WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/GLPK)
  add_dependencies(update_pkgs update_glpk)
endif()

add_custom_target(update_clp
  COMMAND git fetch --all && git reset --hard origin/master && make install
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/CLP)
add_dependencies(update_pkgs update_clp)

add_custom_target(update_filib
  COMMAND git fetch --all && git reset --hard origin/master && make install
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/FILIB)
add_dependencies(update_pkgs update_filib)

add_custom_target(update_picosat
  COMMAND git fetch --all && git reset --hard origin/master && mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/picosat && cp picosat.h ${CMAKE_CURRENT_BINARY_DIR}/include/picosat && cp libpicosat.a ${CMAKE_CURRENT_BINARY_DIR}/lib
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/PICOSAT)
add_dependencies(update_pkgs update_picosat)

add_custom_target(update_ibex
  COMMAND git fetch --all && git reset --hard origin/master && ./waf install
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/IBEX
  DEPENDS update_filib update_clp)
add_dependencies(update_pkgs update_ibex)

add_custom_target(update_nlopt
  COMMAND git fetch --all && git reset --hard origin/master && make install
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/NLOPT)
add_dependencies(update_pkgs update_nlopt)

if(SUPPORT_ODE)
  add_custom_target(update_capd
    COMMAND git fetch --all && git reset --hard origin/master && make install
    WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/CAPD4)
  add_dependencies(update_pkgs update_capd)
endif()

add_custom_target(update_catch
  COMMAND git fetch --all && git reset --hard origin/master && mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/catch && cp -v single_include/catch.hpp ${CMAKE_CURRENT_BINARY_DIR}/include/catch/
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/CATCH)
add_dependencies(update_pkgs update_catch)

add_custom_target(update_easyloggingpp
  COMMAND git fetch --all && git reset --hard origin/master && mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/easylogingpp && cp -v src/easylogging++.h ${CMAKE_CURRENT_BINARY_DIR}/include/easylogingpp/
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/EASYLOGGINGPP)
add_dependencies(update_pkgs update_easyloggingpp)

add_custom_target(update_ezoptionparser
  COMMAND git fetch --all && git reset --hard origin/master && mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/ezOptionParser/ && make PREFIX=${CMAKE_CURRENT_BINARY_DIR} install
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/EZOPTIONPARSER)
add_dependencies(update_pkgs update_ezoptionparser)

add_custom_target(update_json
  COMMAND git fetch --all && git reset --hard origin/master && mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/json && cp -v src/json.hpp ${CMAKE_CURRENT_BINARY_DIR}/include/json/
  WORKING_DIRECTORY ${DREAL_BINARY_DIR}/external/src/JSON)
add_dependencies(update_pkgs update_json)

# Add a distclean target to the Makefile
ADD_CUSTOM_TARGET(distclean
  COMMAND ${CMAKE_BUILD_TOOL} "clean"
  COMMAND ${CMAKE_COMMAND} -P "${CMAKE_MODULE_PATH}/distclean.cmake"
)
