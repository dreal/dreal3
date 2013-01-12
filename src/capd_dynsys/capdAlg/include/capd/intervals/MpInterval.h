/////////////////////////////////////////////////////////////////////////////
/// @file MpInterval.h
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifdef __HAVE_MPFR__

#ifndef _CAPD_INTERVAL_MPINTERVAL_H_ 
#define _CAPD_INTERVAL_MPINTERVAL_H_ 

#include "capd/intervals/Interval.hpp"

#include "capd/multiPrec/MpReal.h"
namespace capd{
namespace intervals{

typedef capd::multiPrec::MpReal MpReal;
typedef capd::multiPrec::MpReal MpfrClass;
typedef Interval<MpReal, MpReal> MpInterval;

}}

#include "capd/intervals/MpInterval_Fun.hpp"

#endif // _CAPD_INTERVAL_MPINTERVAL_H_

#endif


