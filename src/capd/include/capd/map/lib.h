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

#ifndef _CAPD_MAP_LIB_H_
#define _CAPD_MAP_LIB_H_
#include "capd/vectalg/lib.h"
#include "capd/map/Function.h"
#include "capd/map/Map.h"
#include "capd/map/C2Map.h"
#include "capd/map/CnMap.h"
#include "capd/map/CnCoeff.h"
#include "capd/map/DefaultOrder.h"

namespace capd{

typedef capd::map::Function<IVector> IFunction;
typedef capd::map::CnMap<IMatrix,1> IMap;
typedef capd::map::CnMap<IMatrix,2> IC2Map;
typedef capd::map::CnMap<IMatrix,CN_DEFAULT_ORDER> ICnMap;
typedef capd::map::CnCoeff<IMatrix> ICnCoeff;

typedef capd::map::Function<DVector> DFunction;
typedef capd::map::CnMap<DMatrix,1> DMap;
typedef capd::map::C2Map<DMatrix> DC2Map;
typedef capd::map::CnMap<DMatrix,CN_DEFAULT_ORDER> DCnMap;
typedef capd::map::CnCoeff<DMatrix> DCnCoeff;

} // end of namespace capd

#endif // _CAPD_MAP_LIB_H_
