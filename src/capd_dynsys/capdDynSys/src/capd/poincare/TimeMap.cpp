
/////////////////////////////////////////////////////////////////////////////
/// @file TimeMap.cpp
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/map/lib.h"
#include "capd/dynsys/lib.h"
#include "capd/poincare/TimeMap.hpp"

template class capd::poincare::TimeMap<capd::ITaylor>;
template class capd::poincare::TimeMap<capd::ICnTaylor>;

template class capd::poincare::TimeMap<capd::DTaylor>;
