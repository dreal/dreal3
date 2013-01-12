
/////////////////////////////////////////////////////////////////////////////
/// @file dynsetLib.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_DYNSETLIB_H_ 
#define _CAPD_DYNSET_DYNSETLIB_H_ 

#include "capd/intervals/DoubleInterval.h"
#include "capd/intervals/LongDoubleInterval.h"
#include "capd/vectalg/vectalgLib.h"

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

typedef interval (*v_form)(IVector &);

typedef capd::dynset::C0Set<IMatrix> C0Set;
typedef capd::dynset::BallSet<IMatrix> BallSet;
typedef capd::dynset::EllipsoidSet<DVector,IMatrix> EllipsoidSet;
typedef capd::dynset::FlowballSet<IMatrix> FlowballSet;
typedef capd::dynset::Intv2Set<IMatrix> Intv2Set;
typedef capd::dynset::IntervalSet<IMatrix> IntervalSet;
typedef capd::dynset::Pped2Set<IMatrix> Pped2Set;
typedef capd::dynset::PpedSet<IMatrix> PpedSet;
typedef capd::dynset::Rect2Set<IMatrix> Rect2Set;
typedef capd::dynset::RectSet<IMatrix> RectSet;

typedef capd::dynset::C1Set<IMatrix> C1Set;
typedef capd::dynset::C1Rect<IMatrix> C1Rect;
typedef capd::dynset::C1Rect2<IMatrix> C1Rect2;
typedef capd::dynset::C11Rect2<IMatrix> C11Rect2;

typedef capd::dynset::C2Set<IMatrix> C2Set;
typedef capd::dynset::C2Rect2<IMatrix> C2Rect2;

typedef capd::dynset::CnSet<IMatrix> CnSet;
typedef capd::dynset::CnRect2<IMatrix> CnRect2;


typedef capd::dynset::C0Set<IMatrixMD> C0SetMD;
typedef capd::dynset::BallSet<IMatrixMD> BallSetMD;
typedef capd::dynset::EllipsoidSet<DVectorMD,IMatrixMD> EllipsoidSetMD;
typedef capd::dynset::FlowballSet<IMatrixMD> FlowballSetMD;
typedef capd::dynset::Intv2Set<IMatrixMD> Intv2SetMD;
typedef capd::dynset::IntervalSet<IMatrixMD> IntervalSetMD;
typedef capd::dynset::Pped2Set<IMatrixMD> Pped2SetMD;
typedef capd::dynset::PpedSet<IMatrixMD> PpedSetMD;
typedef capd::dynset::Rect2Set<IMatrixMD> Rect2SetMD;
typedef capd::dynset::RectSet<IMatrixMD> RectSetMD;

typedef capd::dynset::C1Set<IMatrixMD> C1SetMD;
typedef capd::dynset::C1Rect<IMatrixMD> C1RectMD;
typedef capd::dynset::C1Rect2<IMatrixMD> C1Rect2MD;
typedef capd::dynset::C11Rect2<IMatrixMD> C11Rect2MD;

typedef capd::dynset::C2Set<IMatrixMD> C2SetMD;
typedef capd::dynset::C2Rect2<IMatrixMD> C2Rect2MD;

typedef capd::dynset::CnSet<IMatrixMD> CnSetMD;
typedef capd::dynset::CnRect2<IMatrixMD> CnRect2MD;


#if (CAPD_CPU_ARCH==CAPD_CPU_ARCH_X86)

  typedef capd::dynset::C0Set<LIMatrix> LIC0Set;
  typedef capd::dynset::BallSet<LIMatrix> LIBallSet;
  typedef capd::dynset::EllipsoidSet<LDVector,LIMatrix> LIEllipsoidSet;
  typedef capd::dynset::FlowballSet<LIMatrix> LIFlowballSet;
  typedef capd::dynset::Intv2Set<LIMatrix> LIntv2Set;
  typedef capd::dynset::IntervalSet<LIMatrix> LIIntervalSet;
  typedef capd::dynset::Pped2Set<LIMatrix> LIPped2Set;
  typedef capd::dynset::PpedSet<LIMatrix> LIPpedSet;
  typedef capd::dynset::Rect2Set<LIMatrix> LIRect2Set;
  typedef capd::dynset::RectSet<LIMatrix> LIRectSet;

  typedef capd::dynset::C1Set<LIMatrix> LIC1Set;
  typedef capd::dynset::C1Rect<LIMatrix> LIC1Rect;
  typedef capd::dynset::C1Rect2<LIMatrix> LIC1Rect2;
  typedef capd::dynset::C11Rect2<LIMatrix> LIC11Rect2;

  typedef capd::dynset::C2Set<LIMatrix> LIC2Set;
  typedef capd::dynset::C2Rect2<LIMatrix> LIC2Rect2;

  typedef capd::dynset::CnSet<LIMatrix> LICnSet;
  typedef capd::dynset::CnRect2<LIMatrix> LICnRect2;



  typedef capd::dynset::C0Set<LIMatrixMD> LIC0SetMD;
  typedef capd::dynset::BallSet<LIMatrixMD> LIBallSetMD;
  typedef capd::dynset::EllipsoidSet<LDVectorMD,LIMatrixMD> LIEllipsoidSetMD;
  typedef capd::dynset::FlowballSet<LIMatrixMD> LIFlowballSetMD;
  typedef capd::dynset::Intv2Set<LIMatrixMD> LIntv2SetMD;
  typedef capd::dynset::IntervalSet<LIMatrixMD> LIIntervalSetMD;
  typedef capd::dynset::Pped2Set<LIMatrixMD> LIPped2SetMD;
  typedef capd::dynset::PpedSet<LIMatrixMD> LIPpedSetMD;
  typedef capd::dynset::Rect2Set<LIMatrixMD> LIRect2SetMD;
  typedef capd::dynset::RectSet<LIMatrixMD> LIRectSetMD;

  typedef capd::dynset::C1Set<LIMatrixMD> LIC1SetMD;
  typedef capd::dynset::C1Rect<LIMatrixMD> LIC1RectMD;
  typedef capd::dynset::C1Rect2<LIMatrixMD> LIC1Rect2MD;
  typedef capd::dynset::C11Rect2<LIMatrixMD> LIC11Rect2MD;

  typedef capd::dynset::C2Set<LIMatrixMD> LIC2SetMD;
  typedef capd::dynset::C2Rect2<LIMatrixMD> LIC2Rect2MD;

  typedef capd::dynset::CnSet<LIMatrixMD> LICnSetMD;
  typedef capd::dynset::CnRect2<LIMatrixMD> LICnRect2MD;

#endif

#ifdef __HAVE_MPFR__

  typedef capd::dynset::C0Set<MpIMatrix> MpC0Set;
  typedef capd::dynset::BallSet<MpIMatrix> MpBallSet;
  typedef capd::dynset::EllipsoidSet<MpVector,MpIMatrix> MpEllipsoidSet;
  typedef capd::dynset::FlowballSet<MpIMatrix> MpFlowballSet;
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




  typedef capd::dynset::C0Set<MpIMatrixMD> MpC0SetMD;
  typedef capd::dynset::BallSet<MpIMatrixMD> MpBallSetMD;
  typedef capd::dynset::EllipsoidSet<MpVectorMD,MpIMatrixMD> MpEllipsoidSetMD;
  typedef capd::dynset::FlowballSet<MpIMatrixMD> MpFlowballSetMD;
  typedef capd::dynset::Intv2Set<MpIMatrixMD> MpIntv2SetMD;
  typedef capd::dynset::IntervalSet<MpIMatrixMD> MpIntervalSetMD;
  typedef capd::dynset::Pped2Set<MpIMatrixMD> MpPped2SetMD;
  typedef capd::dynset::PpedSet<MpIMatrixMD> MpPpedSetMD;
  typedef capd::dynset::Rect2Set<MpIMatrixMD> MpRect2SetMD;
  typedef capd::dynset::RectSet<MpIMatrixMD> MpRectSetMD;

  typedef capd::dynset::C1Set<MpIMatrixMD> MpC1SetMD;
  typedef capd::dynset::C1Rect<MpIMatrixMD> MpC1RectMD;
  typedef capd::dynset::C1Rect2<MpIMatrixMD> MpC1Rect2MD;
  typedef capd::dynset::C11Rect2<MpIMatrixMD> MpC11Rect2MD;

  typedef capd::dynset::C2Set<MpIMatrixMD> MpC2SetMD;
  typedef capd::dynset::C2Rect2<MpIMatrixMD> MpC2Rect2MD;

  typedef capd::dynset::CnSet<MpIMatrixMD> MpCnSetMD;
  typedef capd::dynset::CnRect2<MpIMatrixMD> MpCnRect2MD;

#endif

#endif // _CAPD_DYNSET_DYNSETLIB_H_ 
