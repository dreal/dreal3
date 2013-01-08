


/////////////////////////////////////////////////////////////////////////////
/// @file Intv2Set.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/vectalg/mplib.h"
#include "capd/dynset/Intv2Set.hpp"


#ifdef __HAVE_MPFR__
  template class capd::dynset::Intv2Set<capd::MpIMatrix >;
 #endif


