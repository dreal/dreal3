// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FactorReorganization.cpp
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/capdlib.h"
#include "capd/dynset/C0Rect2Set.hpp"
#include "capd/dynset/FactorReorganization.h"
#include "capd/dynset/ReorganizedSet.h"
using namespace capd;
typedef capd::dynset::C0Rect2Set<IMatrix> BaseSet;
typedef capd::dynset::ReorganizedSet<BaseSet, capd::dynset::FactorReorganization<BaseSet> >  SetType;


#define FIXTURE_NAME FactorReorganization

#include "AffineSetCommonTest.hpp"
#include "DoubletonSetSpecific.hpp"
#include "FactorReorganizationSpecific.hpp"

/// @}
