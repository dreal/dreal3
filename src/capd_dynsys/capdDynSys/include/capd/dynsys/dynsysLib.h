/// @addtogroup dynsys
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file dynsysLib.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2005 */

#ifndef _CAPD_DYNSYS_DYNSYSLIB_H_ 
#define _CAPD_DYNSYS_DYNSYSLIB_H_ 

#include "capd/basicalg/factrial.h"
#include "capd/map/Map.h"
#include "capd/map/C2Map.h"
#include "capd/map/CnMap.h"
#include "capd/dynsys/TaylorException.h"
#include "capd/dynsys/C2Taylor.h"
#include "capd/dynsys/CnTaylor.h"
#include "capd/dynsys/Linear2d.h"
#include "capd/dynsys/Linear3d.h"
#include "capd/dynsys/VLin3D.h"
#include "capd/dynsys/OdeNumTaylor.h"
#include "capd/vectalg/vectalgLib.h"
#include "capd/map/mapLib.h"

typedef capd::dynsys::DynSys<IMatrix> DynSys;
typedef capd::dynsys::Ode<IMatrix> Ode;
typedef capd::dynsys::OdeNum<IMatrix> OdeNum;
typedef capd::dynsys::OdeNumTaylor<IMatrix> OdeNumTaylor;
typedef capd::dynsys::VLin3D<IMatrix> VLin3D;
typedef capd::dynsys::Linear2d<IMatrix> linear2d;
typedef capd::dynsys::Linear3d<IMatrix> linear3d;
typedef capd::dynsys::Taylor<IMap> Taylor;
typedef capd::dynsys::C2Taylor<IC2Map> C2Taylor;
typedef capd::dynsys::CnTaylor<ICnMap> CnTaylor;
typedef capd::dynsys::TaylorException<IVector> TaylorException;


typedef capd::dynsys::DynSys<IMatrixMD> DynSysMD;
typedef capd::dynsys::Ode<IMatrixMD> OdeMD;
typedef capd::dynsys::OdeNum<IMatrixMD> OdeNumMD;
typedef capd::dynsys::OdeNumTaylor<IMatrixMD> OdeNumTaylorMD;
typedef capd::dynsys::VLin3D<IMatrixMD> VLin3DMD;
typedef capd::dynsys::Linear2d<IMatrixMD> linear2dMD;
typedef capd::dynsys::Linear3d<IMatrixMD> linear3dMD;
typedef capd::dynsys::Taylor<IMapMD> TaylorMD;
typedef capd::dynsys::C2Taylor<IC2MapMD> C2TaylorMD;
typedef capd::dynsys::CnTaylor<ICnMapMD> CnTaylorMD;
typedef capd::dynsys::TaylorException<IVectorMD> TaylorExceptionMD;

// classes for nonrigorous computations

typedef capd::dynsys::BasicTaylor<DMap> BasicTaylor;
typedef capd::dynsys::BasicC2Taylor<DC2Map> BasicC2Taylor;
typedef capd::dynsys::BasicCnTaylor<DCnMap> BasicCnTaylor;

typedef capd::dynsys::BasicTaylor<LDMap> LDTaylor;
typedef capd::dynsys::BasicC2Taylor<LDC2Map> LDC2Taylor;
typedef capd::dynsys::BasicCnTaylor<LDCnMap> LDCnTaylor;

typedef capd::dynsys::BasicTaylor<DMapMD> BasicTaylorMD;
typedef capd::dynsys::BasicC2Taylor<DC2MapMD> BasicC2TaylorMD;
typedef capd::dynsys::BasicCnTaylor<DCnMapMD> BasicCnTaylorMD;

typedef capd::dynsys::BasicTaylor<LDMapMD> LDTaylorMD;
typedef capd::dynsys::BasicC2Taylor<LDC2MapMD> LDC2TaylorMD;
typedef capd::dynsys::BasicCnTaylor<LDCnMapMD> LDCnTaylorMD;



#if (CAPD_CPU_ARCH==CAPD_CPU_ARCH_X86)

  typedef capd::dynsys::DynSys<LIMatrix> LIDynSys;
  typedef capd::dynsys::Ode<LIMatrix> LIOde;
  typedef capd::dynsys::OdeNum<LIMatrix> LIOdeNum;
  typedef capd::dynsys::OdeNumTaylor<LIMatrix> LIOdeNumTaylor;
  typedef capd::dynsys::VLin3D<LIMatrix> LIVLin3D;
  typedef capd::dynsys::Linear2d<LIMatrix> LIlinear2d;
  typedef capd::dynsys::Linear3d<LIMatrix> LIlinear3d;
  typedef capd::dynsys::Taylor<LIMap> LITaylor;
  typedef capd::dynsys::C2Taylor<LIC2Map> LIC2Taylor;
  typedef capd::dynsys::CnTaylor<LICnMap> LICnTaylor;
  typedef capd::dynsys::TaylorException<LIVector> LITaylorException;

  typedef capd::dynsys::DynSys<LIMatrixMD> LIDynSysMD;
  typedef capd::dynsys::Ode<LIMatrixMD> LIOdeMD;
  typedef capd::dynsys::OdeNum<LIMatrixMD> LIOdeNumMD;
  typedef capd::dynsys::OdeNumTaylor<LIMatrixMD> LIOdeNumTaylorMD;
  typedef capd::dynsys::VLin3D<LIMatrixMD> LIVLin3DMD;
  typedef capd::dynsys::Linear2d<LIMatrixMD> LIlinear2dMD;
  typedef capd::dynsys::Linear3d<LIMatrixMD> LIlinear3dMD;
  typedef capd::dynsys::Taylor<LIMapMD> LITaylorMD;
  typedef capd::dynsys::C2Taylor<LIC2MapMD> LIC2TaylorMD;
  typedef capd::dynsys::CnTaylor<LICnMapMD> LICnTaylorMD;
  typedef capd::dynsys::TaylorException<LIVectorMD> LITaylorExceptionMD;

#endif



#ifdef __HAVE_MPFR__

  typedef capd::dynsys::DynSys<MpIMatrix> MpDynSys;
  typedef capd::dynsys::Ode<MpIMatrix> MpOde;
  typedef capd::dynsys::OdeNum<MpIMatrix> MpOdeNum;
  typedef capd::dynsys::OdeNumTaylor<MpIMatrix> MpOdeNumTaylor;
  typedef capd::dynsys::VLin3D<MpIMatrix> MpVLin3D;
  typedef capd::dynsys::Linear2d<MpIMatrix> MpLinear2d;
  typedef capd::dynsys::Linear3d<MpIMatrix> MpLinear3d;
  typedef capd::dynsys::Taylor<MpIMap> MpTaylor;
  typedef capd::dynsys::C2Taylor<MpIC2Map> MpC2Taylor;
  typedef capd::dynsys::CnTaylor<MpICnMap> MpCnTaylor;
  typedef capd::dynsys::TaylorException<MpIVector> MpTaylorException;

  // classes for nonrigorous computations
  typedef capd::dynsys::BasicTaylor<MpMap> MpBasicTaylor;
  typedef capd::dynsys::BasicC2Taylor<MpC2Map> MpBasicC2Taylor;
  typedef capd::dynsys::BasicCnTaylor<MpCnMap> MpBasicCnTaylor;



  typedef capd::dynsys::DynSys<MpIMatrixMD> MpDynSysMD;
  typedef capd::dynsys::Ode<MpIMatrixMD> MpOdeMD;
  typedef capd::dynsys::OdeNum<MpIMatrixMD> MpOdeNumMD;
  typedef capd::dynsys::OdeNumTaylor<MpIMatrixMD> MpOdeNumTaylorMD;
  typedef capd::dynsys::VLin3D<MpIMatrixMD> MpVLin3DMD;
  typedef capd::dynsys::Linear2d<MpIMatrixMD> MpLinear2dMD;
  typedef capd::dynsys::Linear3d<MpIMatrixMD> MpLinear3dMD;
  typedef capd::dynsys::Taylor<MpIMapMD> MpTaylorMD;
  typedef capd::dynsys::C2Taylor<MpIC2MapMD> MpC2TaylorMD;
  typedef capd::dynsys::CnTaylor<MpICnMapMD> MpCnTaylorMD;
  typedef capd::dynsys::TaylorException<MpIVectorMD> MpTaylorExceptionMD;

  // classes for nonrigorous computations
  typedef capd::dynsys::BasicTaylor<MpMapMD> MpBasicTaylorMD;
  typedef capd::dynsys::BasicC2Taylor<MpC2MapMD> MpBasicC2TaylorMD;
  typedef capd::dynsys::BasicCnTaylor<MpCnMapMD> MpBasicCnTaylorMD;

#endif

#endif // _CAPD_DYNSYS_DYNSYSLIB_H_ 

/// @}
