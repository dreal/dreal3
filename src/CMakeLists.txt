cmake_minimum_required(VERSION 3.1.3)
project(DREAL C CXX)
set(DREAL_VERSION_MAJOR 3)
set(DREAL_VERSION_MINOR 16)
set(DREAL_VERSION_PATCH 12)
set(PACKAGE_NAME dReal)
set(PACKAGE_VERSION "${DREAL_VERSION_MAJOR}.${DREAL_VERSION_MINOR}.${DREAL_VERSION_PATCH}")
set(PACKAGE_STRING "${PACKAGE_NAME} ${PACKAGE_VERSION}")
set(PACKAGE_BUGREPORT "http://github.com/dreal/dreal3/issues")
set(BUG_REPORT_URL "${PACKAGE_BUGREPORT}" CACHE STRING "Default URL where bug reports are to be submitted.")

set(CMAKE_COLOR_MAKEFILE ON)

if(DEFINED BUILD_SHARED_LIB)
  message(WARNING "The BUILD_SHARED_LIB option is deprecated. Use BUILD_SHARED_LIBS instead.")
else()
  set(BUILD_SHARED_LIB OFF)
endif()

option(SUPPORT_ODE      "Support ODE" ON)
option(LOGGING          "Enable Logging" ON)
option(BUILD_STATIC_BIN "Build static binary"  OFF)
option(BUILD_SHARED_LIBS "Build shared libraries" ${BUILD_SHARED_LIB})
option(USE_LOCAL_THIRD_PARTY "Use local third party libraries" OFF)
option(USE_GLPK         "Use GLPK" ON)
option(USE_NLOPT        "Use NLOPT" ON)
option(TCMALLOC         "Use tcmalloc (a.k.a. gperftools)" OFF)
option(USE_ASAN         "Use address sanitizer (-fsanitize=address)" OFF)

include(CTest)
include(ExternalProject)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

################################################################
# CXX Flags
################################################################
set(DREAL_EXTRA_CXX_FLAGS "-mfpmath=sse -msse -msse2")
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
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -Wno-deprecated-register ${DREAL_EXTRA_CXX_FLAGS}")
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

################################################################
# Shared Lib
################################################################
if(BUILD_STATIC_BIN AND BUILD_SHARED_LIBS)
  message(FATAL_ERROR "Can't handle both of BUILD_STATIC_BIN and BUILD_SHARED_LIBS options." )
endif()
if((NOT APPLE) AND BUILD_SHARED_LIBS)
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
# tcmalloc
################################################################
if(NOT BUILD_STATIC_BIN AND TCMALLOC)
    find_package(Tcmalloc QUIET)
    if(${Tcmalloc_FOUND})
        set(EXTRA_LIBS ${EXTRA_LIBS} ${Tcmalloc_LIBRARIES})
        message(STATUS "Using Tcmalloc.")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D HAS_TCMALLOC")
    else()
        message(STATUS "Failed to find tcmalloc, using standard malloc.")
    endif()
else()
    message(STATUS "Using standard malloc.")
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
SET(EXTERNAL_CXX_FLAGS "${EXTERNAL_CXX_FLAGS} -std=c++11")
JOIN("${DREAL_EXTRA_LINKER_FLAGS}" "," EXTERNAL_LD_FLAGS)

################################################################
# External: PICOSAT
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(PICOSAT
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/picosat.zip
    CONFIGURE_COMMAND ${CMAKE_COMMAND} -E env CC=${CMAKE_C_COMPILER} sh ./configure.sh
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/include/picosat && cp picosat.h ${CMAKE_CURRENT_BINARY_DIR}/include/picosat && cp libpicosat.a ${CMAKE_CURRENT_BINARY_DIR}/lib)
else()
  ExternalProject_Add(PICOSAT
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/picosat.git
    GIT_TAG 8ea4bd467e9dcb3b37e212293f541a2be18f6406
    UPDATE_COMMAND ""
    CONFIGURE_COMMAND ${CMAKE_COMMAND} -E env CC=${CMAKE_C_COMPILER} sh ./configure.sh
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    LOG_DOWNLOAD 1
    LOG_UPDATE 1
    LOG_CONFIGURE 1
    LOG_BUILD 1
    LOG_TEST 1
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
        PATCH_COMMAND autoreconf -if
        CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/FILIB/configure
            CC=${CMAKE_C_COMPILER}
            CXX=${CMAKE_CXX_COMPILER}
            "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
            "LDFLAGS=${EXTERNAL_LD_FLAGS}"
            --prefix=${CMAKE_CURRENT_BINARY_DIR}
            ${SHARED_LIB_CONFIG_COMMAND}
        BUILD_COMMAND make
        INSTALL_COMMAND make install)
else()
    ExternalProject_Add(FILIB
        PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
        GIT_REPOSITORY https://github.com/dreal-deps/filibxx.git
        GIT_TAG d898fe000e157f44e4a84b8f79b4e7556a5d6fb5
        PATCH_COMMAND autoreconf -if
        UPDATE_COMMAND ""
        CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/FILIB/configure
            CC=${CMAKE_C_COMPILER}
            CXX=${CMAKE_CXX_COMPILER}
            "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
            "LDFLAGS=${EXTERNAL_LD_FLAGS}"
            --prefix=${CMAKE_CURRENT_BINARY_DIR}
            ${SHARED_LIB_CONFIG_COMMAND}
        BUILD_COMMAND make
        LOG_DOWNLOAD 1
        LOG_UPDATE 1
        LOG_CONFIGURE 1
        LOG_BUILD 1
        LOG_TEST 1
        LOG_INSTALL 1
        INSTALL_COMMAND make install)
endif()
set(EXTRA_LIBS "prim" ${EXTRA_LIBS})

################################################################
# External: GLPK
################################################################
if(USE_GLPK)
    find_package(GLPK QUIET)
    if (GLPK_FOUND)
        message(STATUS "Found GLPK ${GLPK_VERSION_STRING} in system")
        include_directories(GLPK_INCLUDE_DIR)
        set(EXTRA_LIBS ${GLPK_LIBRARIES} ${EXTRA_LIBS})
    else()
        if(USE_LOCAL_THIRD_PARTY)
            ExternalProject_Add(GLPK
                PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
                URL ${CMAKE_SOURCE_DIR}/third_party/glpk.zip
                PATCH_COMMAND autoreconf -if
                CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/GLPK/configure
                    CC=${CMAKE_C_COMPILER}
                    CXX=${CMAKE_CXX_COMPILER}
                    "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
                    "LDFLAGS=${EXTERNAL_LD_FLAGS}"
                    --prefix=${CMAKE_CURRENT_BINARY_DIR}
                    ${SHARED_LIB_CONFIG_COMMAND}
                BUILD_COMMAND make
                INSTALL_COMMAND make install)
        else()
            ExternalProject_Add(GLPK
                PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
                GIT_REPOSITORY https://github.com/dreal-deps/glpk.git
                GIT_TAG 44ea53eed46d26e1c0ee815ee3e862ba181b1327
                PATCH_COMMAND autoreconf -if
                UPDATE_COMMAND ""
                CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/GLPK/configure
                    CC=${CMAKE_C_COMPILER}
                    CXX=${CMAKE_CXX_COMPILER}
                    "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
                    "LDFLAGS=${EXTERNAL_LD_FLAGS}"
                    --prefix=${CMAKE_CURRENT_BINARY_DIR}
                    ${SHARED_LIB_CONFIG_COMMAND}
                BUILD_COMMAND make
                BUILD_IN_SOURCE 1
                LOG_DOWNLOAD 1
                LOG_UPDATE 1
                LOG_CONFIGURE 1
                LOG_BUILD 1
                LOG_TEST 1
                LOG_INSTALL 1
                INSTALL_COMMAND make install)
        endif()
        set(EXTRA_LIBS "glpk" ${EXTRA_LIBS})
    endif()
endif()

################################################################
# External: NLOPT
################################################################
if(USE_NLOPT)
    find_package(NLOPT QUIET)
    if (NLOPT_FOUND)
        message(STATUS "Found NLOPT ${NLOPT_VERSION_STRING} in system")
        include_directories(${NLOPT_INCLUDE_DIRS})
        set(EXTRA_LIBS ${NLOPT_LIBRARIES} ${EXTRA_LIBS})
    else()
        if(USE_LOCAL_THIRD_PARTY)
            ExternalProject_Add(NLOPT
                PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
                URL ${CMAKE_SOURCE_DIR}/third_party/nlopt.zip
                PATCH_COMMAND autoreconf -if
                CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/NLOPT/configure
                CC=${CMAKE_C_COMPILER}
                CXX=${CMAKE_CXX_COMPILER}
                "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
                "LDFLAGS=${EXTERNAL_LD_FLAGS}"
                --prefix=${CMAKE_CURRENT_BINARY_DIR}
                ${SHARED_LIB_CONFIG_COMMAND}
                --without-guile
                --without-python
                --without-octave
                --without-matlab
                BUILD_COMMAND make
                INSTALL_COMMAND make install)
        else()
            ExternalProject_Add(NLOPT
                PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
                GIT_REPOSITORY https://github.com/dreal-deps/nlopt.git
                GIT_TAG dbf99e4bcea03c68063299ae77657a71151aa23a
                PATCH_COMMAND autoreconf -if
                UPDATE_COMMAND ""
                CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/NLOPT/configure
                CC=${CMAKE_C_COMPILER}
                CXX=${CMAKE_CXX_COMPILER}
                "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
                "LDFLAGS=${EXTERNAL_LD_FLAGS}"
                --prefix=${CMAKE_CURRENT_BINARY_DIR}
                ${SHARED_LIB_CONFIG_COMMAND}
                --without-guile
                --without-python
                --without-octave
                --without-matlab
                BUILD_COMMAND make
                BUILD_IN_SOURCE 1
                LOG_DOWNLOAD 1
                LOG_UPDATE 1
                LOG_CONFIGURE 1
                LOG_BUILD 1
                LOG_TEST 1
                LOG_INSTALL 1
                INSTALL_COMMAND make install)
        endif()
        set(EXTRA_LIBS "nlopt" ${EXTRA_LIBS})
    endif()
endif()

################################################################
# External: ADEPT
################################################################
if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(ADEPT
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/adept.zip
    PATCH_COMMAND autoreconf -if
    CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/ADEPT/configure
        CC=${CMAKE_C_COMPILER}
        CXX=${CMAKE_CXX_COMPILER}
        "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
        "LDFLAGS=${EXTERNAL_LD_FLAGS}"
        --prefix=${CMAKE_CURRENT_BINARY_DIR}
        ${SHARED_LIB_CONFIG_COMMAND}
        --disable-openmp
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND make install)
else()
  ExternalProject_Add(ADEPT
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/adept.git
    GIT_TAG 266ffc0282fcc49716915574647c06be9333e2dc
    PATCH_COMMAND autoreconf -if
    UPDATE_COMMAND ""
    CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/ADEPT/configure
        CC=${CMAKE_C_COMPILER}
        CXX=${CMAKE_CXX_COMPILER}
        "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
        "LDFLAGS=${EXTERNAL_LD_FLAGS}"
        --prefix=${CMAKE_CURRENT_BINARY_DIR}
        ${SHARED_LIB_CONFIG_COMMAND}
        --disable-openmp
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    LOG_DOWNLOAD 1
    LOG_UPDATE 1
    LOG_CONFIGURE 1
    LOG_BUILD 1
    LOG_TEST 1
    LOG_INSTALL 1
    INSTALL_COMMAND make install)
endif()
set(EXTRA_LIBS "adept" ${EXTRA_LIBS})

if(SUPPORT_ODE)
  ################################################################
  # External: CAPD-DynSys-4.0
  ################################################################
  if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(CAPD4
    DEPENDS FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/capdDynSys-4.0.zip
    PATCH_COMMAND autoreconf -if
    CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/CAPD4/configure
        CC=${CMAKE_C_COMPILER}
        CXX=${CMAKE_CXX_COMPILER}
        "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
        "LDFLAGS=${EXTERNAL_LD_FLAGS}"
        --prefix=${CMAKE_CURRENT_BINARY_DIR}
        --without-gui
        --without-boost
        --with-mpfr=no
        --with-filib=no
        --enable-asserts=no
        ${SHARED_LIB_CONFIG_COMMAND}
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND make install)
  else()
    ExternalProject_Add(CAPD4
      DEPENDS FILIB
      PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
      GIT_REPOSITORY https://github.com/dreal-deps/capdDynSys-4.0.git
      GIT_TAG f39f3942dd1bd4899821316efc0ca55483ab5071
      PATCH_COMMAND autoreconf -if
      UPDATE_COMMAND ""
      CONFIGURE_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/CAPD4/configure
          CC=${CMAKE_C_COMPILER}
          CXX=${CMAKE_CXX_COMPILER}
          "CXXFLAGS=${EXTERNAL_CXX_FLAGS}"
          "LDFLAGS=${EXTERNAL_LD_FLAGS}"
          --prefix=${CMAKE_CURRENT_BINARY_DIR}
          --without-gui
          --without-boost
          --with-mpfr=no
          --with-filib=no
          --enable-asserts=no
          ${SHARED_LIB_CONFIG_COMMAND}
      BUILD_COMMAND make
      BUILD_IN_SOURCE 1
      LOG_DOWNLOAD 1
      LOG_UPDATE 1
      LOG_CONFIGURE 1
      LOG_BUILD 1
      LOG_TEST 1
      LOG_INSTALL 1
      INSTALL_COMMAND make install)
  endif()
  set(EXTRA_LIBS "capd" ${EXTRA_LIBS})
endif()

################################################################
# External: CLP
################################################################
find_package(CLP)
if(CLP_FOUND)
    set(USE_CLP ON)
    set(EXTRA_LIBS ${CLP_LIBRARIES} ${EXTRA_LIBS})
    link_directories(${CLP_LIBRARY_DIRS})
    include_directories(${CLP_INCLUDE_DIRS})
else()
    unset(CLP_LIBRARIES)
endif()

################################################################
# External: ibex
################################################################
if(CMAKE_BUILD_TYPE MATCHES "DEBUG")
    set(IBEX_DEBUG_MODE "--with-debug")
    message(STATUS "Use IBEX option ${IBEX_DEBUG_MODE}")
endif()

if(NOT CLP_FOUND)
    set(IBEX_USE_CLP "--without-lp")
    message(STATUS "Use IBEX option ${IBEX_USE_CLP}")
endif()

if(USE_LOCAL_THIRD_PARTY)
  ExternalProject_Add(IBEX
    DEPENDS FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    URL ${CMAKE_SOURCE_DIR}/third_party/ibex-lib.zip
    BUILD_IN_SOURCE 1
    CONFIGURE_COMMAND ${CMAKE_COMMAND} -E env CXX=${CMAKE_CXX_COMPILER} CXXFLAGS=--std=c++11 CC=${CMAKE_C_COMPILER}
        ${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf configure
        --with-optim
        --prefix=${CMAKE_CURRENT_BINARY_DIR}
        --with-filib=${CMAKE_CURRENT_BINARY_DIR}
        ${IBEX_USE_CLP}
        ${IBEX_DEBUG_MODE}
        ${SHARED_LIB_IBEX_COMMAND}
    BUILD_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf build
    INSTALL_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf install)
else()
  ExternalProject_Add(IBEX
    DEPENDS FILIB
    PREFIX ${CMAKE_CURRENT_BINARY_DIR}/external
    GIT_REPOSITORY https://github.com/dreal-deps/ibex-lib.git
    GIT_TAG 874d370fa23a0b56ec72565489e75149d4f2829e
    UPDATE_COMMAND ""
    BUILD_IN_SOURCE 1
    CONFIGURE_COMMAND ${CMAKE_COMMAND} -E env CXX=${CMAKE_CXX_COMPILER} CXXFLAGS=--std=c++11 CC=${CMAKE_C_COMPILER}
        ${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf configure
        --with-optim
        --prefix=${CMAKE_CURRENT_BINARY_DIR}
        --with-filib=${CMAKE_CURRENT_BINARY_DIR}
        ${IBEX_USE_CLP}
        ${IBEX_DEBUG_MODE}
        ${SHARED_LIB_IBEX_COMMAND}
    BUILD_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf build
    BUILD_IN_SOURCE 1
    LOG_DOWNLOAD 1
    LOG_UPDATE 1
    LOG_CONFIGURE 1
    LOG_BUILD 1
    LOG_TEST 1
    INSTALL_COMMAND ${CMAKE_CURRENT_BINARY_DIR}/external/src/IBEX/waf install)
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
    GIT_TAG 5aa2b82b17aeeb935919b1d0bbb93bd0adc86ddb
    UPDATE_COMMAND ""
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
    GIT_TAG efcadc8649c959403dcdeeafbb24f958c05c866e
    UPDATE_COMMAND ""
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
    GIT_TAG 2bdb6b0b75dfdc8614b05f0a1945b8b623bd040b
    UPDATE_COMMAND ""
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
    GIT_TAG 9f9d293bad3792cb7120901b0d5ea7e93fc09b66
    UPDATE_COMMAND ""
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
# Include Directories
################################################################
include_directories(${DREAL_SOURCE_DIR})
include_directories(${DREAL_SOURCE_DIR}/opensmt)
configure_file("${DREAL_SOURCE_DIR}/version.h.in" "${DREAL_BINARY_DIR}/version.h")
configure_file("${DREAL_SOURCE_DIR}/config.h.in" "${DREAL_BINARY_DIR}/dreal_config.h")
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
# PARSER: DRH
################################################################
# Create custom command for flex/lex (note the outputs)
ADD_CUSTOM_COMMAND(
  COMMAND ${FLEX_EXECUTABLE}
  ARGS -o ${DREAL_BINARY_DIR}/opensmt/parsers/drh/drhlexer.cc -Pdrh
  ${DREAL_SOURCE_DIR}/opensmt/parsers/drh/drhlexer.ll
  DEPENDS ${DREAL_SOURCE_DIR}/opensmt/parsers/drh/drhlexer.ll
  OUTPUT  ${DREAL_BINARY_DIR}/opensmt/parsers/drh/drhlexer.cc
  )

# Create custom command for bison/yacc (note the DEPENDS)
ADD_CUSTOM_COMMAND(
  COMMAND ${BISON_EXECUTABLE}
  ARGS -d --name-prefix=drh -y ${DREAL_SOURCE_DIR}/opensmt/parsers/drh/drhparser.yy
  -o ${DREAL_BINARY_DIR}/opensmt/parsers/drh/drhparser.cc
  DEPENDS ${DREAL_BINARY_DIR}/opensmt/parsers/drh/drhlexer.cc
  DEPENDS ${DREAL_SOURCE_DIR}/opensmt/parsers/drh/drhparser.yy
  OUTPUT  ${DREAL_BINARY_DIR}/opensmt/parsers/drh/drhparser.cc
  )
# Since parser.c does not exists yet when cmake is run, mark
# it as generated
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/drh/drhparser.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/drh/drhlexer.cc GENERATED)
SET_SOURCE_FILES_PROPERTIES(${DREAL_BINARY_DIR}/opensmt/parsers/drh/drhlexer.cc PROPERTIES COMPILE_FLAGS -Wno-sign-compare)
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
add_subdirectory(hybrid)

SET(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${DREAL_BINARY_DIR}/lib")
SET(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${DREAL_BINARY_DIR}/lib")
if((NOT APPLE) AND BUILD_SHARED_LIBS)
  add_library(dreal SHARED ${DREAL_SRCS})
  add_library(dop SHARED ${DOP_SRCS})
else()
  add_library(dreal STATIC ${DREAL_SRCS})
  add_library(dop STATIC ${DOP_SRCS})
endif()

if((NOT APPLE) AND BUILD_SHARED_LIBS)
  set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} ${DREAL_EXTRA_LINKER_FLAGS} ${EXTERNAL_LD_FLAGS}")

  target_link_libraries(dreal ${EXTRA_LIBS})
  if(${PYTHONLIBS_FOUND})
    target_link_libraries(dop dreal ${PYTHON_LIBRARIES} ${EXTRA_LIBS})
  else()
    target_link_libraries(dop dreal ${EXTRA_LIBS})
  endif()
endif()

add_dependencies(dop PICOSAT)
add_dependencies(dop IBEX)
add_dependencies(dop ADEPT)
add_dependencies(dop EASYLOGGINGPP)
add_dependencies(dop EZOPTIONPARSER)
add_dependencies(dop JSON)
add_dependencies(dreal PICOSAT)
add_dependencies(dreal IBEX)
add_dependencies(dreal ADEPT)
add_dependencies(dreal EASYLOGGINGPP)
add_dependencies(dreal EZOPTIONPARSER)
add_dependencies(dreal JSON)

if(USE_NLOPT AND (NOT NLOPT_FOUND))
    add_dependencies(dreal NLOPT)
    add_dependencies(dop NLOPT)
endif()
if(USE_GLPK AND (NOT GLPK_FOUND))
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
set(COMP_CMAKE_PATH "${CMAKE_SOURCE_DIR}/cmake/Modules" CACHE INTERNAL "")
include(CompBase)
comp_target_features(dReal-bin PUBLIC cpp11_lang/thread_local)
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
if(BUILD_TESTING)
  add_subdirectory(tests/adept)
  add_subdirectory(tests/c_api)
  add_subdirectory(tests/contractor)
  add_subdirectory(tests/cpp_api)
  add_subdirectory(tests/dr)
  add_subdirectory(tests/ibex)
  add_subdirectory(tests/nra)
  add_subdirectory(tests/util)
  if(USE_NLOPT)
    add_subdirectory(tests/nlopt)
  endif()
  if(USE_GLPK)
    add_subdirectory(tests/glpk)
  endif()
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

if(BUILD_TESTING)
  # Include style check
  include(StyleCheck)
  file(GLOB_RECURSE DREAL_SOURCES
    ${DREAL_SOURCE_DIR}/api/*.C           ${DREAL_SOURCE_DIR}/api/*.cpp
    ${DREAL_SOURCE_DIR}/api/*.h           ${DREAL_SOURCE_DIR}/api/*.hh
    ${DREAL_SOURCE_DIR}/constraint/*.cpp  ${DREAL_SOURCE_DIR}/constraint/*.h
    ${DREAL_SOURCE_DIR}/contractor/*.cpp  ${DREAL_SOURCE_DIR}/contractor/*.h
    ${DREAL_SOURCE_DIR}/dsolvers/*.cpp    ${DREAL_SOURCE_DIR}/dsolvers/*.h
    ${DREAL_SOURCE_DIR}/icp/*.cpp         ${DREAL_SOURCE_DIR}/icp/*.h
    ${DREAL_SOURCE_DIR}/optimizer/*.cpp   ${DREAL_SOURCE_DIR}/optimizer/*.h
    ${DREAL_SOURCE_DIR}/tests/*.cpp       ${DREAL_SOURCE_DIR}/tests/*.h
    ${DREAL_SOURCE_DIR}/tools/dop/*.cpp   ${DREAL_SOURCE_DIR}/tools/dop/*.h
    ${DREAL_SOURCE_DIR}/util/*.cpp        ${DREAL_SOURCE_DIR}/util/*.h)
  add_style_check_target(style "${DREAL_SOURCES}")
  add_test(NAME style_check COMMAND ${DREAL_SOURCE_DIR}/cmake/Modules/cpplint.py ${DREAL_SOURCES})
endif()
ADD_CUSTOM_COMMAND(TARGET dReal-bin
          POST_BUILD
          COMMAND ${CMAKE_COMMAND} -E make_directory ${DREAL_SOURCE_DIR}/../bin
          COMMAND ${CMAKE_COMMAND} -E copy ${DREAL_BINARY_DIR}/dReal ${DREAL_SOURCE_DIR}/../bin/)
if(NOT BUILD_STATIC_BIN)
  ADD_CUSTOM_COMMAND(TARGET dOp-bin
            POST_BUILD
            COMMAND ${CMAKE_COMMAND} -E make_directory ${DREAL_SOURCE_DIR}/../bin
            COMMAND ${CMAKE_COMMAND} -E copy ${DREAL_BINARY_DIR}/dOp ${DREAL_SOURCE_DIR}/../bin/)
endif()

# Add target 'format' which uses clang-format
find_program(CLANG_FORMAT "clang-format"
    NAMES clang-format clang-format-4.0 clang-format-3.9 clang-format-3.8 clang-format-3.7 clang-format-3.6 clang-format-3.5 clang-format-3.4 clang-format-3.3)
if(CLANG_FORMAT)
    add_custom_target(format
        COMMAND ${CLANG_FORMAT}
        -i
        -style=file
        ${DREAL_SOURCES})
else()
    message(WARNING "clang-format is not found. No build target is created for 'format'.")
endif()

#########################################
# CPack
#########################################
set(CPACK_PACKAGE_NAME dReal)
string(TOLOWER ${CMAKE_SYSTEM_NAME} LOWER_SYSTEM_NAME)
if(BUILD_SHARED_LIBS)
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
# PKG CONFIG
########################################
SET(PKG_CONFIG_LIBDIR "\${prefix}/lib/dreal")
SET(PKG_CONFIG_INCLUDEDIR "\${prefix}/include/dreal")
SET(PROJECT_DESCRIPTION "nonlinear SMT Solver")
SET(PKG_CONFIG_LIBS "-L\${libdir} -ldreal -libex -ladept")
if(SUPPORT_ODE)
    SET(PKG_CONFIG_LIBS "${PKG_CONFIG_LIBS} -lcapd")
endif()
if(USE_CLP)
    foreach(CLP_LIB ${CLP_LIBRARIES})
        SET(PKG_CONFIG_LIBS "${PKG_CONFIG_LIBS} -l${CLP_LIB}")
    endforeach()
endif()
if(USE_NLOPT)
    SET(PKG_CONFIG_LIBS "${PKG_CONFIG_LIBS} -lnlopt")
endif()
if(USE_GLPK)
    SET(PKG_CONFIG_LIBS "${PKG_CONFIG_LIBS} -lglpk")
endif()
SET(PKG_CONFIG_LIBS "${PKG_CONFIG_LIBS} -lprim -lpicosat ${CMAKE_THREAD_LIBS_INIT} -lm")
SET(PKG_CONFIG_CFLAGS "-I\${includedir}")

CONFIGURE_FILE("${CMAKE_CURRENT_SOURCE_DIR}/pkg-config.pc.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/dreal.pc")

########################################
# CMAKE CONFIG FILES
########################################
set(DREAL_INCLUDE_DIR include/dreal)
set(DREAL_LIBRARY_DIR lib/dreal)
set(DREAL_LIBRARIES dreal ibex adept)
if(SUPPORT_ODE)
    list(APPEND DREAL_LIBRARIES capd)
endif()
if(USE_CLP)
    list(APPEND DREAL_LIBRARIES ${CLP_LIBRARIES})
endif()
if(USE_NLOPT)
    list(APPEND DREAL_LIBRARIES nlopt)
endif()
if(USE_GLPK)
    list(APPEND DREAL_LIBRARIES glpk)
endif()
list(APPEND DREAL_LIBRARIES prim picosat ${CMAKE_THREAD_LIBS_INIT} m)
include(CMakePackageConfigHelpers)
configure_package_config_file(dreal-config.cmake.in dreal-config.cmake
    INSTALL_DESTINATION "${DREAL_LIBRARY_DIR}"
    PATH_VARS DREAL_INCLUDE_DIR DREAL_LIBRARY_DIR
    NO_CHECK_REQUIRED_COMPONENTS_MACRO)
write_basic_package_version_file(dreal-config-version.cmake
  VERSION ${PACKAGE_VERSION} COMPATIBILITY AnyNewerVersion)

########################################
# INSTALL
########################################
install(DIRECTORY "${DREAL_BINARY_DIR}/lib/"
    DESTINATION "${DREAL_LIBRARY_DIR}"
    FILES_MATCHING
    PATTERN "*.a"
    PATTERN "*.la"
    PATTERN "*.so"
    PATTERN "*.dylib")
install(DIRECTORY "${DREAL_SOURCE_DIR}/api/"
    DESTINATION "${DREAL_INCLUDE_DIR}"
    FILES_MATCHING
    PATTERN "*.h"
    PATTERN "*.hh")
install(FILES "${DREAL_BINARY_DIR}/dreal.pc" DESTINATION lib/pkgconfig)
install(FILES "${DREAL_BINARY_DIR}/dreal_config.h"
    DESTINATION "${DREAL_INCLUDE_DIR}")
install(FILES
  "${DREAL_BINARY_DIR}/dreal-config.cmake"
  "${DREAL_BINARY_DIR}/dreal-config-version.cmake"
  DESTINATION "${DREAL_LIBRARY_DIR}")
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
if(BUILD_SHARED_LIBS)
  install(DIRECTORY "${DREAL_BINARY_DIR}/lib"
          DESTINATION ".")
  install(FILES "${DREAL_SOURCE_DIR}/opensmt/api/opensmt_c.h"
          DESTINATION "include")
endif()

if(APPLE AND BUILD_SHARED_LIBS)
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,-all_load ${EXTERNAL_LD_FLAGS}")

    add_library(dreal-shared SHARED /dev/null)
    set_target_properties(dreal-shared PROPERTIES
      LINKER_LANGUAGE CXX
      OUTPUT_NAME dreal)
    target_link_libraries(dreal-shared dreal ${EXTRA_LIBS})
endif()

# Add a distclean target to the Makefile
ADD_CUSTOM_TARGET(distclean
  COMMAND ${CMAKE_BUILD_TOOL} "clean"
  COMMAND ${CMAKE_COMMAND} -P "${CMAKE_MODULE_PATH}/distclean.cmake")
