/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file poincareLib.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2008 */

#ifndef _CAPD_POINCARE_POINCARELIB_H_ 
#define _CAPD_POINCARE_POINCARELIB_H_ 

#include "capd/poincare/PoincareMap.h"
#include "capd/poincare/TimeMap.h"

#include "capd/dynsys/dynsysLib.h"
#include "capd/dynset/dynsetLib.h"

// classes for nonrigorous computations

typedef capd::poincare::BasicPoincareMap<BasicTaylor> BasicPoincareMap;
typedef capd::poincare::BasicPoincareMap<BasicC2Taylor> BasicC2PoincareMap;
typedef capd::poincare::BasicPoincareMap<BasicCnTaylor> BasicCnPoincareMap;

typedef capd::poincare::PoincareMap<Taylor> PoincareMap;
typedef capd::poincare::PoincareMap<C2Taylor> C2PoincareMap;
typedef capd::poincare::PoincareMap<CnTaylor> CnPoincareMap;


typedef capd::poincare::TimeMap<BasicTaylor> DTimeMap;
typedef capd::poincare::TimeMap<BasicC2Taylor> DC2TimeMap;
typedef capd::poincare::TimeMap<BasicCnTaylor> DCnTimeMap;

typedef capd::poincare::TimeMap<Taylor> ITimeMap;
typedef capd::poincare::TimeMap<C2Taylor> IC2TimeMap;
typedef capd::poincare::TimeMap<CnTaylor> ICnTimeMap;



typedef capd::poincare::BasicPoincareMap<BasicTaylorMD> BasicPoincareMapMD;
typedef capd::poincare::BasicPoincareMap<BasicC2TaylorMD> BasicC2PoincareMapMD;
typedef capd::poincare::BasicPoincareMap<BasicCnTaylorMD> BasicCnPoincareMapMD;

typedef capd::poincare::PoincareMap<TaylorMD> PoincareMapMD;
typedef capd::poincare::PoincareMap<C2TaylorMD> C2PoincareMapMD;
typedef capd::poincare::PoincareMap<CnTaylorMD> CnPoincareMapMD;


typedef capd::poincare::TimeMap<BasicTaylorMD> DTimeMapMD;
typedef capd::poincare::TimeMap<BasicC2TaylorMD> DC2TimeMapMD;
typedef capd::poincare::TimeMap<BasicCnTaylorMD> DCnTimeMapMD;

typedef capd::poincare::TimeMap<TaylorMD> ITimeMapMD;
typedef capd::poincare::TimeMap<C2TaylorMD> IC2TimeMapMD;
typedef capd::poincare::TimeMap<CnTaylorMD> ICnTimeMapMD;

#ifdef __HAVE_MPFR__

  typedef capd::poincare::BasicPoincareMap<MpBasicTaylor> MpBasicPoincareMap;
  typedef capd::poincare::BasicPoincareMap<MpBasicC2Taylor> MpBasicC2PoincareMap;
  typedef capd::poincare::BasicPoincareMap<MpBasicCnTaylor> MpBasicCnPoincareMap;

  typedef capd::poincare::PoincareMap<MpTaylor> MpPoincareMap;
  typedef capd::poincare::PoincareMap<MpC2Taylor> MpC2PoincareMap;
  typedef capd::poincare::PoincareMap<MpCnTaylor> MpCnPoincareMap;


  typedef capd::poincare::TimeMap<MpBasicTaylor> MpTimeMap;
  typedef capd::poincare::TimeMap<MpBasicC2Taylor> MpC2TimeMap;
  typedef capd::poincare::TimeMap<MpBasicCnTaylor> MpCnTimeMap;

  typedef capd::poincare::TimeMap<MpTaylor> MpITimeMap;
  typedef capd::poincare::TimeMap<MpC2Taylor> MpIC2TimeMap;
  typedef capd::poincare::TimeMap<MpCnTaylor> MpICnTimeMap;



  typedef capd::poincare::BasicPoincareMap<MpBasicTaylorMD> MpBasicPoincareMapMD;
  typedef capd::poincare::BasicPoincareMap<MpBasicC2TaylorMD> MpBasicC2PoincareMapMD;
  typedef capd::poincare::BasicPoincareMap<MpBasicCnTaylorMD> MpBasicCnPoincareMapMD;

  typedef capd::poincare::PoincareMap<MpTaylorMD> MpPoincareMapMD;
  typedef capd::poincare::PoincareMap<MpC2TaylorMD> MpC2PoincareMapMD;
  typedef capd::poincare::PoincareMap<MpCnTaylorMD> MpCnPoincareMapMD;


  typedef capd::poincare::TimeMap<MpBasicTaylorMD> MpTimeMapMD;
  typedef capd::poincare::TimeMap<MpBasicC2TaylorMD> MpC2TimeMapMD;
  typedef capd::poincare::TimeMap<MpBasicCnTaylorMD> MpCnTimeMapMD;

  typedef capd::poincare::TimeMap<MpTaylorMD> MpITimeMapMD;
  typedef capd::poincare::TimeMap<MpC2TaylorMD> MpIC2TimeMapMD;
  typedef capd::poincare::TimeMap<MpCnTaylorMD> MpICnTimeMapMD;

#endif

#endif // _CAPD_POINCARE_POINCARELIB_H_ 

/// @}
