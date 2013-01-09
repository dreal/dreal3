
/////////////////////////////////////////////////////////////////////////////
/// @file PoincareMap.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include "capd/interval/lib.h"
#include "capd/vectalg/lib.h"
//#include "capd/vectalg/Matrix.hpp"
//#include "capd/map/CnMap.hpp"
//#include "capd/dynsys/CnTaylor.hpp"
#include "capd/poincare/PoincareMap.hpp"
#include "capd/map/lib.h"
#include "capd/dynsys/lib.h"

template class capd::poincare::BasicPoincareMap<capd::DTaylor>;
template class capd::poincare::BasicPoincareMap<capd::DCnTaylor>;

template class capd::poincare::PoincareMap<capd::ICnTaylor>;

