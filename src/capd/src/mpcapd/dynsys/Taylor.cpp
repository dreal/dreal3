
/////////////////////////////////////////////////////////////////////////////
/// @file Taylor.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* Author: Daniel Wilczak 2001-2005 */

#include "capd/dynsys/BasicTaylor.hpp"
#include "capd/dynsys/Taylor.hpp"
#include "capd/vectalg/mplib.h"
#include "capd/map/mplib.h"

#ifdef __HAVE_MPFR__

  template class capd::dynsys::Taylor<capd::MpIMap>;
  template class capd::dynsys::BasicTaylor<capd::MpIMap>;
  template class capd::dynsys::BasicTaylor<capd::MpMap>;
  template class capd::dynsys::BasicTaylor<capd::MpMap,capd::dynsys::ILastTermsStepControl>;
#endif
