/////////////////////////////////////////////////////////////////////////////
/// @file dos16.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// krak/krak.h include for DOS and WIN 3.1
#  include <stdarg.h>
#  ifdef _krak_c
#    include <stdio.h>
#    include <time.h>
#    include <alloc.h>
#    include <conio.h>
#  endif
#  define HDR 800
#  define VDR 600
#  define MAX_COLOR_NO 16
#  define HG huge

#  define var_head void _FAR *

#  define SC(c,r,g,b) red_c[c]=(BYTE)(255*(r));green_c[c]=(BYTE)(255*(g));blue_c[c]=(BYTE)(255*(b));
#  define COLOR(a) RGB(red_c[a],green_c[a],blue_c[a])
#  define mlalloc farmalloc
#  define lfree farfree
