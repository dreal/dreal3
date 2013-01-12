
/////////////////////////////////////////////////////////////////////////////
/// @file TaylorHOE.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/dynsys/BasicTaylor.hpp"
#include "capd/dynsys/Taylor.hpp"
#include "capd/dynsys/TaylorHOE.hpp"
#include "capd/vectalg/mplib.h"
#include "capd/map/mplib.h"

#ifdef __HAVE_MPFR__

  template class capd::dynsys::TaylorHOE<capd::MpIMap, capd::dynsys::IMpLastTermsStepControl<capd::MpInterval> >;
#endif
