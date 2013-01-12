
/////////////////////////////////////////////////////////////////////////////
/// @file CoordReorganize.cpp
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/vectalg/lib.h"
#include "capd/geomset/DoubletonSet.h"
#include "capd/dynset/CoordWiseReorganization.h"

template class capd::dynset::CoordWiseReorganization<capd::geomset::DoubletonSet< capd::IMatrix > >;
