/////////////////////////////////////////////////////////////////////////////
/// @file CnTaylor.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#include "capd/dynsys/BasicCnTaylor.hpp"
#include "capd/dynsys/CnTaylor.hpp"
#include "capd/map/lib.h"

template class capd::dynsys::BasicCnTaylor<capd::DCnMap>;
template class capd::dynsys::BasicCnTaylor<capd::ICnMap,capd::dynsys::IEncFoundStepControl>;
template class capd::dynsys::CnTaylor<capd::ICnMap>;

