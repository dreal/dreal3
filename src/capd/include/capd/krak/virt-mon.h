/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file virt-mon.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

//krak/krak.h for virtual monitor
#  define MoveTo(x,y) VirtMon.prpos=((y)*VIRT_SCR_COL_NO+(x))
#  define LineTo(x,y) VirtMon.prpos=((y)*VIRT_SCR_COL_NO+(x))
#  define RAINBOW(x) 1
#  define F_HGHT 1
#  define F_WDTH 1
#  define SetBgCol(col)
#  define SetFgCol(col)
//#  include "virtmn_i.h"
#  define MAX_PALETTE 2

/// @}
