//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file poincare/lib.h
///
/// @author Tomasz Kapela   @date 2010-01-23
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_POINCARE_LIB_H_
#define _CAPD_POINCARE_LIB_H_

#include "capd/dynsys/lib.h"
#include "capd/dynset/lib.h"

#include "capd/poincare/PoincareMap.h"
#include "capd/poincare/PoincareMapJet.h"
#include "capd/poincare/TimeMap.h"


namespace capd{

// classes for nonrigorous computations
typedef capd::poincare::BasicPoincareMap<DTaylor> DPoincareMap;
typedef capd::poincare::BasicPoincareMap<DC2Taylor> DC2PoincareMap;
typedef capd::poincare::BasicPoincareMap<DCnTaylor> DCnPoincareMap;

typedef capd::poincare::PoincareMap<ITaylor> IPoincareMap;
typedef capd::poincare::PoincareMap<IC2Taylor> IC2PoincareMap;
typedef capd::poincare::PoincareMap<ICnTaylor> ICnPoincareMap;


typedef capd::poincare::TimeMap<DTaylor> DTimeMap;
typedef capd::poincare::TimeMap<DC2Taylor> DC2TimeMap;
typedef capd::poincare::TimeMap<DCnTaylor> DCnTimeMap;

typedef capd::poincare::TimeMap<ITaylor> ITimeMap;
typedef capd::poincare::TimeMap<IC2Taylor> IC2TimeMap;
typedef capd::poincare::TimeMap<ICnTaylor> ICnTimeMap;

} // end of namespace capd

#endif // _CAPD_POINCARE_LIB_H_
