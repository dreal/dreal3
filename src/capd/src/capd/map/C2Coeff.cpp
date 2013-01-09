
/////////////////////////////////////////////////////////////////////////////
/// @file C2Coeff.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/map/C2Coeff.hpp"
#include "capd/interval/lib.h"

template class capd::map::C2Coeff<double>;
template class capd::map::C2Coeff<long double>;
template class capd::map::C2Coeff<capd::Interval>;
