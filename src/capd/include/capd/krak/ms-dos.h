/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ms-dos.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// krak/krak.h include for IBM DOS
#  ifdef DOS
#    include <dos.h>
#  endif
#  include <graphics.h>
#  define IBM
#  define F_HGHT 10
#  define F_WDTH  8
#  undef BLACK
#  undef BLUE
#  undef GREEN
#  define RAINBOW(x) min(15,max(0,(int)((1.-x)*15)))
#  define SYSTEM "IBM DOS (GR)"
#  define MAX_PALETTE 16
void MoveTo(INT i,INT j);
void LineTo(INT i,INT j);

/// @}
