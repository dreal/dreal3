
/////////////////////////////////////////////////////////////////////////////
/// @file appl-mac.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

//  APPLE MAC
#    include <storage.h>
#    define F_HGHT 12
#    define F_WDTH  8
#    define MAX_COLOR_NO 0

#    define FillRct(r,pattNr,colNr) FillRect(r,patt_pntr[pattNr])
#    define DrawStrng(s) DrawString(CtoPstr(s))
#    define Clock() (TickCount()/60.0)
#
     typedef char *va_list;
#    define va_dcl int va_alist;
#    define va_start(list,lastfix) list=(char *)&lastfix
#    define va_end(list)
#    define va_arg(list,mode) ((mode *)(list+=sizeof(mode)))[-1]
#    define HG
#    define SYSTEM "Mac"

