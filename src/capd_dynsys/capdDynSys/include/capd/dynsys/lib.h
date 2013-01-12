//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file dynsys/lib.h
///
/// @author Tomasz Kapela   @date 2010-01-23
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_LIB_H_
#define _CAPD_DYNSYS_LIB_H_

#include "capd/basicalg/factrial.h"
#include "capd/dynsys/TaylorException.h"
#include "capd/dynsys/TaylorHOE.h"
#include "capd/dynsys/C2Taylor.h"
#include "capd/dynsys/CnTaylor.h"
#include "capd/dynsys/Linear2d.h"
#include "capd/dynsys/Linear3d.h"
#include "capd/dynsys/VLin3D.h"
#include "capd/dynsys/OdeNumTaylor.h"
#include "capd/vectalg/lib.h"
#include "capd/map/lib.h"
namespace capd{

typedef capd::dynsys::DynSys<IMatrix> IDynSys;
typedef capd::dynsys::Ode<IMatrix> IOde;
typedef capd::dynsys::OdeNum<IMatrix> IOdeNum;
typedef capd::dynsys::OdeNumTaylor<IMatrix> IOdeNumTaylor;
typedef capd::dynsys::VLin3D<IMatrix> IVLin3D;
typedef capd::dynsys::Linear2d<IMatrix> ILinear2d;
typedef capd::dynsys::Linear3d<IMatrix> ILinear3d;
typedef capd::dynsys::TaylorHOE<IMap> ITaylor;
typedef capd::dynsys::C2Taylor<IC2Map> IC2Taylor;
typedef capd::dynsys::CnTaylor<ICnMap> ICnTaylor;
typedef capd::dynsys::TaylorException<IVector> ITaylorException;

// classes for nonrigorous computations

typedef capd::dynsys::BasicTaylor<DMap> DTaylor;
typedef capd::dynsys::BasicC2Taylor<DC2Map> DC2Taylor;
typedef capd::dynsys::BasicCnTaylor<DCnMap> DCnTaylor;

} // end of namespace capd

#endif // _CAPD_DYNSYS_LIB_H_
