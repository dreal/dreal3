/////////////////////////////////////////////////////////////////////////////
/// @file LongDoubleInterval.h
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <cmath>

using std::log;

#include "capd/basicalg/doubleFun.h"
#include "capd/intervals/Interval.h"
#include "capd/rounding/DoubleRounding.h"

#ifndef _CAPD_INTERVAL_LONGDOUBLEINTERVAL_H_ 
#define _CAPD_INTERVAL_LONGDOUBLEINTERVAL_H_ 

#if (CAPD_CPU_ARCH==CAPD_CPU_ARCH_X86)

typedef capd::intervals::Interval<long double, capd::rounding::DoubleRounding> LInterval;

//using namespace capd::intervals;
namespace capd{
	namespace intervals{
		typedef capd::intervals::Interval<long double, capd::rounding::DoubleRounding> LongDoubleInterval;
	}
}


#endif // check of architecture

#endif // _CAPD_INTERVAL_LONGDOUBLEINTERVAL_H_ 
