
/////////////////////////////////////////////////////////////////////////////
/// @file capd/diffIncl/DiffInclusionCW.cpp
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/vectalg/lib.h"
#include "capd/map/lib.h"
#include "capd/diffIncl/MultiMap.h"
#include "capd/diffIncl/DiffInclusionCW.hpp"

typedef capd::diffIncl::MultiMap<capd::IMap> MultiMap;

template class capd::diffIncl::DiffInclusionCW<MultiMap>;

