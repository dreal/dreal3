/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

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

// FATAL - 0
// ERROR - 1
// WARNING - 2
// INFO - 3
#pragma once
#include <glog/logging.h>
#include <iosfwd>

#define DREAL_LOG_FATAL   VLOG(0)
#define DREAL_LOG_ERROR   VLOG(1)
#define DREAL_LOG_WARNING VLOG(2)
#define DREAL_LOG_INFO    VLOG(3)
