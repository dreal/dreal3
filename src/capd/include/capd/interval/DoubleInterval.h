//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD
//   Subpackage:
/// @addtogroup intervals
/// @{
 
/////////////////////////////////////////////////////////////////////////////
/// @file DoubleInterval.h
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_INTERVAL_DOUBLEINTERVAL_H_ 
#define _CAPD_INTERVAL_DOUBLEINTERVAL_H_ 

#include <cmath>

using std::log;

#include "capd/capd/doubleFun.h"

#include "capd/interval/Interval.h"

#include "capd/rounding/DoubleRounding.h"


typedef capd::intervals::Interval<double, capd::rounding::DoubleRounding> interval;

extern ::interval pi;

//using namespace capd::intervals;
namespace capd{
	namespace intervals{
		typedef capd::intervals::Interval<double, capd::rounding::DoubleRounding> DoubleInterval;
	}
}

#ifdef __INTERVAL_DEPRECATED__
using capd::intervals::Degenerate;
using capd::intervals::Left;
using capd::intervals::Right;
using capd::intervals::in;
using capd::intervals::intervalHull;
using capd::intervals::iSplit;
using capd::intervals::solve_affine_inclusion;

inline void round_nearest()
{
  capd::rounding::DoubleRounding::roundNearest();
}
    
inline void round_up()
{
  capd::rounding::DoubleRounding::roundUp();
}

    
inline void round_down()
{
  capd::rounding::DoubleRounding::roundDown();
}

    
inline void round_cut()
{
  capd::rounding::DoubleRounding::roundCut();
}

inline void init_fpunit()
{}

inline int rounding_test()
{
  return capd::rounding::DoubleRounding::test();
}

#endif //__INTERVAL_DEPRECATED__

#endif // _CAPD_INTERVAL_DOUBLEINTERVAL_H_ 

/// @}
