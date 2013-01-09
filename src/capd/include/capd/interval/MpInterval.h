/////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
/// @file mpInterval.h
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

#include "capd/interval/Interval.hpp"

#ifndef USE_OLD_MPFRCLASS

#include "capd/multiPrec/MpReal.h"
namespace capd{
namespace intervals{
  typedef capd::multiPrec::MpReal MpReal;
  typedef capd::multiPrec::MpReal MpfrClass;
  typedef Interval<MpReal, MpReal> MpInterval;
}}

#include "capd/interval/MpInterval_Fun.hpp"

#else  // OLD MpfrClass
#include "capd/multiPrec/MpfrClass.h"

namespace capd{
namespace intervals{
  typedef capd::multiPrec::MpfrClass MpReal;
  typedef capd::multiPrec::MpfrClass MpfrClass;
  typedef Interval<MpReal, MpReal>   MpInterval;
}}

#include "capd/interval/MpIntervalFun.h"
#endif // USE_OLD_MPFRCLASS

#endif // _CAPD_INTERVAL_MPINTERVAL_H_

#endif


