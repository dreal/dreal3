
/////////////////////////////////////////////////////////////////////////////
/// @file Function.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/map/Function.hpp"
#include "capd/vectalg/lib.h"
template class capd::map::BasicFunction<double>;
template class capd::map::BasicFunction<capd::Interval>;
template class capd::map::Function<capd::DVector>;
template class capd::map::Function<capd::IVector>;

/// @}
