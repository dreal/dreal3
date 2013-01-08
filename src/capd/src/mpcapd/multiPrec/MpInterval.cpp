
/////////////////////////////////////////////////////////////////////////////
/// @file mpInterval.cpp
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include "capd/multiPrec/MpfrClass.h"
#ifdef USE_OLD_MPFRCLASS
#ifdef __HAVE_MPFR__

// Interval class  and inline functions definitions
#include "capd/multiPrec/MpInterval.h"

// operators definitions
#include "../src/mpcapd/multiPrec/MpInterval_operator.hpp"

// other functions definitions
#include "../src/mpcapd/multiPrec/MpInterval_function.hpp"


#endif  // __HAVE_MPFR__
#endif //USE_OLD_MPFRCLASS
