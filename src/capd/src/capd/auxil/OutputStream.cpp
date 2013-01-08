/// @addtogroup auxil
/// @{
 
/////////////////////////////////////////////////////////////////////////////
///
/// @file OutputStream.cpp
///
/// @author Pawel Pilarczyk, Tomasz Kapela
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk and Tomasz Kapela.
//
// This file constitutes a part of the Homology Library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

// Started in December 1997. Last revision: April 12, 2006.


#include "capd/auxil/OutputStream.h"
#include <iostream>

namespace capd {

// --------------------------------------------------
// ----------------- OUTPUT STREAMS ------------------
// --------------------------------------------------

::capd::auxil::OutputStream scon (std::cout, true, true);
::capd::auxil::OutputStream sout (std::cout, true, true);
::capd::auxil::OutputStream serr (std::cout, true, true);
::capd::auxil::OutputStream slog (std::cout, false, true);
::capd::auxil::OutputStream slog2 (std::cout, false, true);
::capd::auxil::OutputStream slog3 (std::cout, false, true);
::capd::auxil::OutputStream sbug (std::cout, false, true);
::capd::auxil::OutputStream sseq (std::cout, false, false);

}
