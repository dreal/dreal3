
/////////////////////////////////////////////////////////////////////////////
/// @file vectalg/Norm.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/vectalg/lib.h"
#include "capd/vectalg/Norm.hpp"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"

namespace capd{ 
  namespace vectalg{

template class capd::vectalg::Norm<IVector,IMatrix>;
template class capd::vectalg::EuclNorm<IVector,IMatrix>;
template class capd::vectalg::MaxNorm<IVector,IMatrix>;
template class capd::vectalg::SumNorm<IVector,IMatrix>;
template class capd::vectalg::EuclLNorm<IVector,IMatrix>;
template class capd::vectalg::MaxLNorm<IVector,IMatrix>;
template class capd::vectalg::SumLNorm<IVector,IMatrix>;

template class capd::vectalg::Norm<DVector,DMatrix>;
template class capd::vectalg::EuclNorm<DVector,DMatrix>;
template class capd::vectalg::MaxNorm<DVector,DMatrix>;
template class capd::vectalg::SumNorm<DVector,DMatrix>;
template class capd::vectalg::EuclLNorm<DVector,DMatrix>;
template class capd::vectalg::MaxLNorm<DVector,DMatrix>;
template class capd::vectalg::SumLNorm<DVector,DMatrix>;

}}  // end of namespace capd::vectalg


