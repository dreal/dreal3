//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file mpcapd.h
///
/// Multiple Precision version of CAPD library.
///
/// This file includes all mplib.h files from modules
/// that are included in mpcapd library.
/// In general all typedefs have Mp prefix i.e.
/// - MpInterval - interval with multiple precision endpoints
/// - MpVector - vector with multiple precision coefficients
/// - MpIVector -  vector with coefficients of the MpInterval type
///
/// @author Tomasz Kapela   @date 2010-01-22
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_MPCAPD_H_
#define _CAPD_MPCAPD_H_

#include "capd/multiPrec/mplib.h"
#include "capd/interval/mplib.h"
#include "capd/vectalg/mplib.h"
#include "capd/map/mplib.h"
#include "capd/dynset/mplib.h"
#include "capd/dynsys/mplib.h"

#endif // _CAPD_MPCAPD_H_
