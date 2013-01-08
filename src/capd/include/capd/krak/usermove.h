/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file usermove.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_USERMOVE_H_ 
#define _CAPD_KRAK_USERMOVE_H_ 

#include "capd/krak/primitiv.h"

namespace capd{
namespace krak{
class UserMove{
public:
	int key;
	capd::krak::Pxl pxl;

	UserMove(void);
};

void SetUserMove(UserMove &um);
int GetUserMove(UserMove &um);
void WaitUserMove(UserMove& um, capd::krak::Rct &r, int col1, int col2, double freq);
void WaitUserMove(UserMove& um);
}}

#endif // _CAPD_KRAK_USERMOVE_H_ 

/// @}
