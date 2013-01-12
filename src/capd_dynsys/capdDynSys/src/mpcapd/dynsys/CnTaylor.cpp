
/////////////////////////////////////////////////////////////////////////////
/// @file CnTaylor.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2006 */

#include "capd/dynsys/BasicCnTaylor.hpp"
#include "capd/dynsys/CnTaylor.hpp"
#include "capd/map/CnMap.hpp"
#include "capd/map/mplib.h"

#ifdef __HAVE_MPFR__
  template class capd::dynsys::BasicCnTaylor<capd::MpCnMap, capd::dynsys::MpLastTermsStepControl<capd::MpFloat> >;

  template class capd::dynsys::CnTaylor<capd::MpICnMap>;
#endif


