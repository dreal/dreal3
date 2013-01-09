//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD
//   Subpackage:
/// @addtogroup intervals 
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file interval.h
///
/// Interval Arithmetics package 
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_INTERVAL_INTERVAL_H_ 
#define _CAPD_INTERVAL_INTERVAL_H_ 

#include "capd/capd/minmax.h"

// functions defined for templates to work also with double instead of intervals
#include "capd/capd/doubleFun.h"

#include "capd/interval/IntervalSettings.h"

#include "capd/interval/IntervalError.h"

// interval interface and inline functions
#include "capd/interval/Interval.h"

// operators
#include "capd/interval/Interval_Op.hpp"

// external functions
#include "capd/interval/Interval_Fun.hpp"


#ifdef __INTERVAL_DEPRECATED__

// this is temporary 'include' to provide backward compatibility
#include "capd/interval/DoubleInterval.h"

#endif //__INTERVAL_DEPRECATED__

#endif // _CAPD_INTERVAL_INTERVAL_H_ 

/// @}
