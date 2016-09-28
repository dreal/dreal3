# - Try to find CLP
# Once done this will define
#  CLP_FOUND - System has CLP
#  CLP_INCLUDE_DIRS - The CLP include directories
#  CLP_LIBRARIES - The libraries needed to use CLP


find_path(CLP_INCLUDE_DIR
          NAMES "ClpConfig.h"
          PATHS "/usr/include/coin"
                "/usr/local/include/clp/coin"
          NO_DEFAULT_PATH)

get_filename_component(CLP_INCLUDE_DIR ${CLP_INCLUDE_DIR} DIRECTORY)

find_path(COINUTILS_INCLUDE_DIR
          NAMES "CoinPragma.hpp"
          PATHS "/usr/include/coin"
                "/usr/local/include/coinutils/coin"
          NO_DEFAULT_PATH)

find_library(CLP_LIBRARY
             NAMES Clp
             PATHS "/usr/lib"
                   "/usr/local/lib"
                   "/usr/lib/coin")
find_library(COINUTILS_LIBRARY
             NAMES CoinUtils
             PATHS "/usr/lib"
                   "/usr/local/lib")

set(CLP_INCLUDE_DIRS "${CLP_INCLUDE_DIR};${COINUTILS_INCLUDE_DIR}")
set(CLP_LIBRARIES "${CLP_LIBRARY};${COINUTILS_LIBRARY}")

include(FindPackageHandleStandardArgs)
# handle the QUIETLY and REQUIRED arguments and set CLP_FOUND to TRUE
# if all listed variables are TRUE
find_package_handle_standard_args(CLP
    DEFAULT_MSG
    CLP_LIBRARY
    COINUTILS_LIBRARY
    CLP_INCLUDE_DIR
    COINUTILS_INCLUDE_DIR)

mark_as_advanced(CLP_INCLUDE_DIR CLP_LIBRARIES)
