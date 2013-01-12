/////////////////////////////////////////////////////////////////////////////
/// @file DNorm.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_FACADE_DNORM_H_
#define _CAPD_FACADE_DNORM_H_

#include "capd/vectalg/Norm.h"
#include "capd/facade/DMatrix.h"

namespace capd{
namespace facade{

typedef capd::vectalg::Norm<DVector,DMatrix> DNorm;
typedef capd::vectalg::EuclNorm<DVector,DMatrix> DEuclNorm;
typedef capd::vectalg::MaxNorm<DVector,DMatrix> DMaxNorm;
typedef capd::vectalg::SumNorm<DVector,DMatrix> DSumNorm;
typedef capd::vectalg::EuclLNorm<DVector,DMatrix> DEuclLNorm;
typedef capd::vectalg::MaxLNorm<DVector,DMatrix> DMaxLNorm;
typedef capd::vectalg::SumLNorm<DVector,DMatrix> DSumLNorm;

}} // the end of the namespace capd::facade

#endif //define _DNORM_H_

