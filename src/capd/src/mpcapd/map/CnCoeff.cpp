
/////////////////////////////////////////////////////////////////////////////
//
/// @file CnCoeff.cpp
///
/// @author Daniel Wilczak
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/map/CnCoeff.hpp"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/vectalg/mplib.h"


#ifdef __HAVE_MPFR__

namespace capd{
namespace map{

template class capd::map::CnContainer<MpFloat>;
template class capd::map::CnContainer<MpInterval>;

template class capd::map::CnCoeff< MpMatrix >;
template class capd::map::CnCoeff<capd::MpIMatrix >;

}}

#endif
