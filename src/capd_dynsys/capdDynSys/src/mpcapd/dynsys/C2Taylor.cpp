
/////////////////////////////////////////////////////////////////////////////
/// @file C2Taylor.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak 2001-2005 */

#include "capd/dynsys/Taylor.hpp"
#include "capd/dynsys/BasicC2Taylor.hpp"
#include "capd/dynsys/C2Taylor.hpp"
#include "capd/vectalg/mplib.h"
#include "capd/map/mplib.h"


#ifdef __HAVE_MPFR__

template class capd::dynsys::C2Taylor<capd::MpIC2Map>;
template class capd::dynsys::BasicC2Taylor<capd::MpIC2Map>;
template class capd::dynsys::BasicC2Taylor<capd::MpC2Map>;

template class capd::dynsys::BasicTaylor<capd::MpIC2Map>;
template class capd::dynsys::BasicTaylor<capd::MpC2Map>;

#endif

