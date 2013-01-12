//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file dynset/mplib.h
///
/// @author Tomasz Kapela   @date 2010-01-22
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_MPLIB_H_
#define _CAPD_DYNSET_MPLIB_H_

#include "capd/vectalg/mplib.h"

#include "capd/dynset/BallSet.h"
#include "capd/dynset/EllipsoidSet.h"
#include "capd/dynset/FlowballSet.h"
#include "capd/dynset/Intv2Set.h"
#include "capd/dynset/IntervalSet.h"
#include "capd/dynset/Pped2Set.h"
#include "capd/dynset/PpedSet.h"
#include "capd/dynset/Rect2Set.h"
#include "capd/dynset/RectSet.h"

#include "capd/dynset/C1Rect.h"
#include "capd/dynset/C1Rect2.h"
#include "capd/dynset/C11Rect2.h"
#include "capd/dynset/C2Rect2.h"
#include "capd/dynset/CnRect2.h"

#ifdef __HAVE_MPFR__

namespace capd{

/// @addtogroup mpcapdlib
/// @{

 typedef capd::dynset::C0Set<MpIMatrix> MpC0Set;
 typedef capd::dynset::Intv2Set<MpIMatrix> MpIntv2Set;
 typedef capd::dynset::IntervalSet<MpIMatrix> MpIntervalSet;
 typedef capd::dynset::Pped2Set<MpIMatrix> MpPped2Set;
 typedef capd::dynset::PpedSet<MpIMatrix> MpPpedSet;
 typedef capd::dynset::Rect2Set<MpIMatrix> MpRect2Set;
 typedef capd::dynset::RectSet<MpIMatrix> MpRectSet;

 typedef capd::dynset::C1Set<MpIMatrix> MpC1Set;
 typedef capd::dynset::C1Rect<MpIMatrix> MpC1Rect;
 typedef capd::dynset::C1Rect2<MpIMatrix> MpC1Rect2;
 typedef capd::dynset::C11Rect2<MpIMatrix> MpC11Rect2;

 typedef capd::dynset::C2Set<MpIMatrix> MpC2Set;
 typedef capd::dynset::C2Rect2<MpIMatrix> MpC2Rect2;

 typedef capd::dynset::CnSet<MpIMatrix> MpCnSet;
 typedef capd::dynset::CnRect2<MpIMatrix> MpCnRect2;

/// @}
} // end of namespace capd

#endif //__HAVE_MPFR__

#endif // _CAPD_DYNSET_MPLIB_H_
