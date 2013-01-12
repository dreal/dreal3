
/////////////////////////////////////////////////////////////////////////////
/// @file AffineSet.cpp
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.
#include "capd/vectalg/mplib.h"
#include "capd/geomset/AffineSet.hpp"

#ifdef __HAVE_MPFR__
namespace capd{
namespace geomset{
  template class AffineSet<capd::MpIMatrix >;
}}
#endif

