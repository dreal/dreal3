
/////////////////////////////////////////////////////////////////////////////
/// @file algfacade/DNorm.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/intervals/DoubleInterval.h"
#include "capd/facade/DMatrix.h"
#include "capd/vectalg/Norm.hpp"

template class capd::vectalg::Norm<capd::facade::DVector,capd::facade::DMatrix>;
template class capd::vectalg::EuclNorm<capd::facade::DVector,capd::facade::DMatrix>;
template class capd::vectalg::MaxNorm<capd::facade::DVector,capd::facade::DMatrix>;
template class capd::vectalg::SumNorm<capd::facade::DVector,capd::facade::DMatrix>;
template class capd::vectalg::EuclLNorm<capd::facade::DVector,capd::facade::DMatrix>;
template class capd::vectalg::MaxLNorm<capd::facade::DVector,capd::facade::DMatrix>;
template class capd::vectalg::SumLNorm<capd::facade::DVector,capd::facade::DMatrix>;
