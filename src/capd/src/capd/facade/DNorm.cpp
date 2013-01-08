/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DNorm.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/interval/DoubleInterval.h" // for right, etc.
#include "capd/DMatrix.h"
#include "capd/vectalg/Norm.hpp"

namespace capd{

template class capd::vectalg::Norm<DVector,DMatrix>;
template class capd::vectalg::EuclNorm<DVector,DMatrix>;
template class capd::vectalg::MaxNorm<DVector,DMatrix>;
template class capd::vectalg::SumNorm<DVector,DMatrix>;
template class capd::vectalg::EuclLNorm<DVector,DMatrix>;
template class capd::vectalg::MaxLNorm<DVector,DMatrix>;
template class capd::vectalg::SumLNorm<DVector,DMatrix>; 

}

/// @}
