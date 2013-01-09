/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file IVector.cpp
///
/// @author kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

// Created on 4 maj 2008, 06:20


#include "capd/vectalg/Vector.hpp"
#include "capd/IVector.h"

namespace capd{

//template IVector capd::vectalg::intervalHull<IVector>(const IVector &A, const IVector &B);
template void capd::vectalg::split<IVector>(IVector& v, IVector& rv);
template IVector capd::vectalg::midVector<IVector>(const IVector& v);
template IVector capd::vectalg::leftVector<IVector>(const IVector& v);
template IVector capd::vectalg::rightVector<IVector>(const IVector& v);
template interval capd::vectalg::size<IVector>(const IVector& v);
template IVector capd::vectalg::diam<IVector>(const IVector& v);
//template IVector capd::vectalg::intervalBall<IVector>(const IVector &iv, const interval &r);
//template interval capd::vectalg::solveAffineInclusion<IVector>(const IVector& a,const IVector& p,const IVector& c);
//template interval capd::vectalg::solveAffineInclusion<IVector>(const IVector& a,const IVector& p,const IVector& c,int&);
template bool capd::vectalg::subset<IVector>(const IVector& v1, const IVector& v2);
template bool capd::vectalg::subsetInterior<IVector>(const IVector& v1, const IVector& v2);
//template IVector capd::vectalg::intersection<IVector>(const IVector &v1, const IVector &v2);

}

/// @}
