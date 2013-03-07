
/////////////////////////////////////////////////////////////////////////////
/// @file CnCoeff.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/vectalg/lib.h"
#include "capd/map/CnCoeff.hpp"

template class capd::map::CnContainer<double>;
template class capd::map::CnContainer<long double>;
template class capd::map::CnContainer<capd::DInterval>;

template class capd::map::CnCoeff< capd::DMatrix >;
template class capd::map::CnCoeff< capd::IMatrix >;

