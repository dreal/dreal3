
/////////////////////////////////////////////////////////////////////////////
/// @file C2Coeff.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/map/C2Coeff.hpp"
#include "capd/interval/mplib.h"

#ifdef __HAVE_MPFR__

namespace capd{
namespace map{

template class C2Coeff< capd::MpFloat >;
template class C2Coeff< capd::MpInterval>;

}}
#endif
