


/////////////////////////////////////////////////////////////////////////////
/// @file C1Rect.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/vectalg/mplib.h"
#include "capd/dynset/C1Rect.hpp"
#include "capd/vectalg/Matrix.hpp"


#ifdef __HAVE_MPFR__
  template class capd::dynset::C1Rect<capd::MpIMatrix >;
#endif


