/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013 - 2014, Soonho Kong, Sicun Gao, and Edmund Clarke

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
#include <glog/logging.h>
#include <iosfwd>

#define DREAL_FATAL_LEVEL   0
#define DREAL_ERROR_LEVEL   1
#define DREAL_WARNING_LEVEL 2
#define DREAL_INFO_LEVEL    3
#define DREAL_DEBUG_LEVEL   4

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
