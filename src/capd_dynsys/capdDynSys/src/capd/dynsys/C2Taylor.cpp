
/////////////////////////////////////////////////////////////////////////////
/// @file C2Taylor.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#include "capd/vectalg/lib.h"
#include "capd/map/lib.h"
#include "capd/dynsys/Taylor.hpp"
#include "capd/dynsys/BasicC2Taylor.hpp"
#include "capd/dynsys/C2Taylor.hpp"

template class capd::dynsys::C2Taylor<capd::IC2Map>;
template class capd::dynsys::BasicC2Taylor<capd::IC2Map,capd::dynsys::IEncFoundStepControl>;
template class capd::dynsys::BasicC2Taylor<capd::DC2Map>;

template class capd::dynsys::BasicTaylor<capd::IC2Map,capd::dynsys::IEncFoundStepControl>;
template class capd::dynsys::BasicTaylor<capd::DC2Map>;

