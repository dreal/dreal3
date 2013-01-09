/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file maplib.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_MAP_MAPLIB_H_ 
#define _CAPD_MAP_MAPLIB_H_ 

#include "capd/vectalg/vectalgLib.h"
#include "capd/map/Function.h"
#include "capd/map/Map.h"
#include "capd/map/C2Map.h"
#include "capd/map/CnMap.h"

typedef capd::map::Function<IVector> IFunction;
typedef capd::map::CnMap<IMatrix,1> IMap;
typedef capd::map::C2Map<IMatrix> IC2Map;
typedef capd::map::CnMap<IMatrix,3> ICnMap;

typedef capd::map::Function<DVector> DFunction;
typedef capd::map::Map<DMatrix> DMap;
typedef capd::map::C2Map<DMatrix> DC2Map;
typedef capd::map::CnMap<DMatrix,3> DCnMap;

typedef capd::map::Function<LDVector> LDFunction;
typedef capd::map::Map<LDMatrix> LDMap;
typedef capd::map::C2Map<LDMatrix> LDC2Map;
typedef capd::map::CnMap<LDMatrix,3> LDCnMap;

typedef capd::map::Function<IVectorMD> IFunctionMD;
typedef capd::map::Map<IMatrixMD> IMapMD;
typedef capd::map::C2Map<IMatrixMD> IC2MapMD;
typedef capd::map::CnMap<IMatrixMD,3> ICnMapMD;

typedef capd::map::Function<DVectorMD> DFunctionMD;
typedef capd::map::Map<DMatrixMD> DMapMD;
typedef capd::map::C2Map<DMatrixMD> DC2MapMD;
typedef capd::map::CnMap<DMatrixMD,3> DCnMapMD;

typedef capd::map::Function<LDVectorMD> LDFunctionMD;
typedef capd::map::Map<LDMatrixMD> LDMapMD;
typedef capd::map::C2Map<LDMatrixMD> LDC2MapMD;
typedef capd::map::CnMap<LDMatrixMD,3> LDCnMapMD;

#if (CAPD_CPU_ARCH==CAPD_CPU_ARCH_X86)

  typedef capd::map::Function<LIVector> LIFunction;
  typedef capd::map::Map<LIMatrix> LIMap;
  typedef capd::map::C2Map<LIMatrix> LIC2Map;
  typedef capd::map::CnMap<LIMatrix,3> LICnMap;

  typedef capd::map::Function<LIVectorMD> LIFunctionMD;
  typedef capd::map::Map<LIMatrixMD> LIMapMD;
  typedef capd::map::C2Map<LIMatrixMD> LIC2MapMD;
  typedef capd::map::CnMap<LIMatrixMD,3> LICnMapMD;

#endif



#endif // _CAPD_MAP_MAPLIB_H_ 

/// @}
