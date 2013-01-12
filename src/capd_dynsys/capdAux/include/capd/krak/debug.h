
/////////////////////////////////////////////////////////////////////////////
/// @file debug.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#define _DEBUG_INFO

#ifdef _DEBUG_INFO
  #include "capd/krak/krak.h"
  #undef min
  #undef max
#endif
