/////////////////////////////////////////////////////////////////////////////
/// @file algfacade/IVector.cpp
///
/// @author kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

// Created on 4 maj 2008, 06:20



#include "capd/facade/DVector.h"
#include "capd/facade/IVector.h"
#include "capd/vectalg/Vector.hpp"
using namespace capd;

//template facade::IVector vectalg::intervalHull<facade::IVector>(const facade::IVector &A, const facade::IVector &B);
template void vectalg::split<facade::IVector,facade::IVector>(facade::IVector& , facade::IVector& rv);
template void vectalg::split<facade::IVector,facade::DVector>(const facade::IVector& v, facade::DVector& c, facade::IVector& rv);
template facade::IVector vectalg::midVector<facade::IVector>(const facade::IVector& v);
template facade::IVector vectalg::leftVector<facade::IVector>(const facade::IVector& v);
template facade::IVector vectalg::rightVector<facade::IVector>(const facade::IVector& v);
template facade::IVector::ScalarType vectalg::size<facade::IVector>(const facade::IVector& v);
template facade::IVector vectalg::diam<facade::IVector>(const facade::IVector& v);
//template facade::IVector vectalg::intervalBall<facade::IVector>(const facade::IVector &iv, const interval &r);
//template interval vectalg::solveAffineInclusion<facade::IVector>(const facade::IVector& a,const facade::IVector& p,const facade::IVector& c);
//template interval vectalg::solveAffineInclusion<facade::IVector>(const facade::IVector& a,const facade::IVector& p,const facade::IVector& c,int&);
template bool vectalg::subset<facade::IVector>(const facade::IVector& v1, const facade::IVector& v2);
template bool vectalg::subsetInterior<facade::IVector>(const facade::IVector& v1, const facade::IVector& v2);
//template facade::IVector vectalg::intersection<facade::IVector>(const facade::IVector &v1, const facade::IVector &v2);

