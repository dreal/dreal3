/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file INorm.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/IMatrix.h"
#include "capd/vectalg/Norm.hpp"



template class capd::vectalg::Norm<capd::IVector,capd::IMatrix>;
template class capd::vectalg::EuclNorm<capd::IVector,capd::IMatrix>;
template class capd::vectalg::MaxNorm<capd::IVector,capd::IMatrix>;
template class capd::vectalg::SumNorm<capd::IVector,capd::IMatrix>;
template class capd::vectalg::EuclLNorm<capd::IVector,capd::IMatrix>;
template class capd::vectalg::MaxLNorm<capd::IVector,capd::IMatrix>;
template class capd::vectalg::SumLNorm<capd::IVector,capd::IMatrix>; 

/// @}
