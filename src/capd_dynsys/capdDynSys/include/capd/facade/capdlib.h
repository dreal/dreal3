/// @addtogroup simple
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file facade/capdlib.h
///
/// This file includes all facades of the basic classes in the CAPD library.
/// It simplifies the usage of the CAPD library to the beginners
/// Facades are not templates but ordinary classes so compiler logs are
/// clearer and it is easier to start to use them.
/// But they are a little bit slower and sometimes they don't
/// provide whole functionality of the original template class.
/// Also facades are written only for basic classes so at some level
/// you have to use templates. You can use facades as parameters to high level
/// templates.
///
/// @author kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2008 by the CAPD Group.
//
// Distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

// Created on 16 maj 2009

#ifndef _CAPD_FACADE_SIMPLECAPDLIB_H_
#define _CAPD_FACADE_SIMPLECAPDLIB_H_

#include "capd/facade/capdAlglib.h"
#include "capd/facade/Icapdlib.h"
#include "capd/facade/Dcapdlib.h"

#endif // _CAPD_FACADE_SIMPLECAPDLIB_H_

/// @}
