//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD
//   Subpackage:
/// @addtogroup xxx
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C0Pped2SetTest.cpp
///
///
/// @author kapela  @date 2009-12-09
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) CAPD group 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 


#include "capd/capdlib.h"
#include "capd/dynset/C0Pped2Set.hpp"

template class capd::dynset::C0Pped2Set<capd::IMatrix>;
typedef capd::dynset::C0Pped2Set<capd::IMatrix> SetType;

#define FIXTURE_NAME C0Pped2SetTest
#include "AffineSetCommonTest.hpp"
#include "CenteredDoubletonSpecific.hpp"

/// @}
