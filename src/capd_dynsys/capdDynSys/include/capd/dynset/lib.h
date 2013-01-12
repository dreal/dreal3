//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file dynset/lib.h
///
/// @author Tomasz Kapela   @date 2010-01-23
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_LIB_H_
#define _CAPD_DYNSET_LIB_H_
#include "capd/vectalg/lib.h"

#include "capd/dynset/BallSet.h"
#include "capd/dynset/EllipsoidSet.h"
#include "capd/dynset/FlowballSet.h"
#include "capd/dynset/Intv2Set.h"
#include "capd/dynset/IntervalSet.h"
#include "capd/dynset/Pped2Set.h"
#include "capd/dynset/PpedSet.h"
#include "capd/dynset/Rect2Set.h"
#include "capd/dynset/RectSet.h"
#include "capd/dynset/C0Rect2RSet.h"

#include "capd/dynset/C1Rect.h"
#include "capd/dynset/C1Rect2RSet.h"
#include "capd/dynset/C11Rect2.h"
#include "capd/dynset/C2Rect2.h"
#include "capd/dynset/CnRect2.h"

namespace capd{

typedef DInterval (*v_form)(IVector &);

/// @addtogroup capdlib
/// @{

typedef capd::dynset::C0Set<IMatrix> C0Set;
typedef capd::dynset::BallSet<IMatrix> BallSet;
typedef capd::dynset::EllipsoidSet<DVector,IMatrix> EllipsoidSet;
typedef capd::dynset::FlowballSet<IMatrix> FlowballSet;
typedef capd::dynset::Intv2Set<IMatrix> Intv2Set;
typedef capd::dynset::IntervalSet<IMatrix> IntervalSet;
typedef capd::dynset::Pped2Set<IMatrix> C0Pped2Set;
typedef capd::dynset::PpedSet<IMatrix> C0PpedSet;
typedef capd::dynset::Rect2Set<IMatrix> C0Rect2Set;
typedef capd::dynset::C0Rect2RSet<IMatrix> C0Rect2RSet;
typedef capd::dynset::RectSet<IMatrix> C0RectSet;

typedef capd::dynset::C1Set<IMatrix> C1Set;
typedef capd::dynset::C1Rect<IMatrix> C1RectSet;
typedef capd::dynset::C1Rect2RSet<IMatrix> C1Rect2Set;
typedef capd::dynset::C1Rect2RSet<IMatrix> C1Rect2RSet;
typedef capd::dynset::C11Rect2<IMatrix> C11Rect2Set;

typedef capd::dynset::C2Set<IMatrix> C2Set;
typedef capd::dynset::C2Rect2<IMatrix> C2Rect2Set;
typedef C2Rect2Set C2Rect2;

typedef capd::dynset::CnSet<IMatrix> CnSet;
typedef capd::dynset::CnRect2<IMatrix> CnRect2Set;

/// @}
} // end of namespace capd

#endif // _CAPD_DYNSET_LIB_H_
