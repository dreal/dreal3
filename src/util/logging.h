/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2015, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#pragma once
#include "./config.h"

#define DREAL_FATAL_LEVEL   0
#define DREAL_ERROR_LEVEL   1
#define DREAL_WARNING_LEVEL 2
#define DREAL_INFO_LEVEL    3
#define DREAL_DEBUG_LEVEL   4

#ifdef LOGGING

#define ELPP_CUSTOM_COUT std::cerr
#define ELPP_NO_DEFAULT_LOG_FILE
#define ELPP_DISABLE_DEFAULT_CRASH_HANDLING
#define ELPP_THREAD_SAFE
#include <easylogingpp/easylogging++.h>
#include <iosfwd>

#define DREAL_LOG_FATAL   VLOG(DREAL_FATAL_LEVEL)
#define DREAL_LOG_ERROR   VLOG(DREAL_ERROR_LEVEL)
#define DREAL_LOG_WARNING VLOG(DREAL_WARNING_LEVEL)
#define DREAL_LOG_INFO    VLOG(DREAL_INFO_LEVEL)
#define DREAL_LOG_DEBUG   VLOG(DREAL_DEBUG_LEVEL)

#define DREAL_LOG_FATAL_IS_ON   VLOG_IS_ON(DREAL_FATAL_LEVEL)
#define DREAL_LOG_ERROR_IS_ON   VLOG_IS_ON(DREAL_ERROR_LEVEL)
#define DREAL_LOG_WARNING_IS_ON VLOG_IS_ON(DREAL_WARNING_LEVEL)
#define DREAL_LOG_INFO_IS_ON    VLOG_IS_ON(DREAL_INFO_LEVEL)
#define DREAL_LOG_DEBUG_IS_ON   VLOG_IS_ON(DREAL_DEBUG_LEVEL)

#else

#include <iostream>
#include <iosfwd>
#define DREAL_LOG_FATAL   if (false) std::cerr
#define DREAL_LOG_ERROR   if (false) std::cerr
#define DREAL_LOG_WARNING if (false) std::cerr
#define DREAL_LOG_INFO    if (false) std::cerr
#define DREAL_LOG_DEBUG   if (false) std::cerr

#define DREAL_LOG_FATAL_IS_ON   false
#define DREAL_LOG_ERROR_IS_ON   false
#define DREAL_LOG_WARNING_IS_ON false
#define DREAL_LOG_INFO_IS_ON    false
#define DREAL_LOG_DEBUG_IS_ON   false

#endif
