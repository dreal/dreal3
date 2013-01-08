
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
#include "capd/vectalg/mplib.h"

#ifdef __HAVE_MPFR__

  template class capd::diffAlgebra::Curve<capd::MpIMatrix>;
  template class capd::diffAlgebra::Curve<capd::MpMatrix>;

#endif
