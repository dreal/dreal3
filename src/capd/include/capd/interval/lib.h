//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file lib.h
///
/// @author Tomasz Kapela   @date 2010-01-23
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INTERVAL_LIB_H_
#define _CAPD_INTERVAL_LIB_H_

#ifndef __USE_FILIB__

#include "capd/interval/DoubleInterval.h"
namespace capd{
typedef capd::intervals::DoubleInterval Interval;
typedef capd::intervals::DoubleInterval DInterval;
} // end of namespace capd

#else

#include "capd/filib/Interval.h"
namespace capd{
typedef ::capd::filib::Interval<double, ::filib::native_directed, ::filib::i_mode_normal >  DInterval;
typedef DInterval Interval;
typedef DInterval interval;

} // end of namespace capd

#endif

#endif // _CAPD_INTERVAL_LIB_H_
