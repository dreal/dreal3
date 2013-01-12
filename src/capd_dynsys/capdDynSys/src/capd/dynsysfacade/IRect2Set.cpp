/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file IRect2Set.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include "capd/facade/IRect2Set.h"
#include "capd/dynset/C0Rect2Set.hpp"
#include "capd/vectalg/iobject.hpp"

template class capd::dynset::C0Rect2Set<capd::facade::IMatrix>;

/// @}
