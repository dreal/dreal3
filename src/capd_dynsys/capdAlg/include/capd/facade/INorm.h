/////////////////////////////////////////////////////////////////////////////
/// @file INorm.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_FACADE_INORM_H_
#define _CAPD_FACADE_INORM_H_

#include "capd/vectalg/Norm.h"
#include "capd/facade/IMatrix.h"

namespace capd{
namespace facade{

typedef capd::vectalg::Norm<IVector,IMatrix> INorm;
typedef capd::vectalg::EuclNorm<IVector,IMatrix> IEuclNorm;
typedef capd::vectalg::MaxNorm<IVector,IMatrix> IMaxNorm;
typedef capd::vectalg::SumNorm<IVector,IMatrix> ISumNorm;
typedef capd::vectalg::EuclLNorm<IVector,IMatrix> IEuclLNorm;
typedef capd::vectalg::MaxLNorm<IVector,IMatrix> IMaxLNorm;
typedef capd::vectalg::SumLNorm<IVector,IMatrix> ISumLNorm;
 
}} // the end of the namespace capd::facade

#endif //define _CAPD_FACADE_INORM_H_

