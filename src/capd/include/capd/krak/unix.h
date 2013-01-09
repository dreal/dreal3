/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file unix.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// krak/krak.h include for UNIX operating systems
#  define MAX_COLOR_NO 16
#  define MAX_PALETTE 216
#  define F_HGHT 15
#  define F_WDTH 9
#  define RAINBOW(x) min(15,max(0,(int)((1.-x)*15)))
namespace capd{
namespace krak{
	void MoveTo(int,int); 
	void LineTo(int,int);
}}
#  include <stdio.h>
#  include <stdarg.h>
#  define mlalloc malloc
#  define lfree free
	void *malloc();
#  define HG

/// @}
