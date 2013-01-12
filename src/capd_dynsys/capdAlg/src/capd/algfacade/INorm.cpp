/////////////////////////////////////////////////////////////////////////////
/// @file algfacade/INorm.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/facade/IMatrix.h"
#include "capd/vectalg/Norm.hpp"



template class capd::vectalg::Norm<capd::facade::IVector,capd::facade::IMatrix>;
template class capd::vectalg::EuclNorm<capd::facade::IVector,capd::facade::IMatrix>;
template class capd::vectalg::MaxNorm<capd::facade::IVector,capd::facade::IMatrix>;
template class capd::vectalg::SumNorm<capd::facade::IVector,capd::facade::IMatrix>;
template class capd::vectalg::EuclLNorm<capd::facade::IVector,capd::facade::IMatrix>;
template class capd::vectalg::MaxLNorm<capd::facade::IVector,capd::facade::IMatrix>;
template class capd::vectalg::SumLNorm<capd::facade::IVector,capd::facade::IMatrix>;
