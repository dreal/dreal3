
/////////////////////////////////////////////////////////////////////////////
/// @file Curve.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 


#include "capd/diffAlgebra/Curve.hpp"
#include "capd/vectalg/lib.h"

template class capd::diffAlgebra::Curve<capd::DMatrix>;
template class capd::diffAlgebra::Curve<capd::IMatrix>;
