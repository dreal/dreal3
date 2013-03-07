
/////////////////////////////////////////////////////////////////////////////
/// @file mpcapd/vectalg/Container.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <iostream>
#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Container.hpp"
#include "capd/intervals/mplib.h"

namespace capd{ 
  namespace vectalg{

#ifdef __HAVE_MPFR__

template class capd::vectalg::Container<MpFloat,CAPD_DEFAULT_DIMENSION>;
template class capd::vectalg::Container<MpInterval,CAPD_DEFAULT_DIMENSION>;

#endif

  }
}
