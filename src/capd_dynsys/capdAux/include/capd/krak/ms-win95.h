/////////////////////////////////////////////////////////////////////////////
/// @file ms-win95.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

// krak/krak.h include for MS WINDOWS 95

#  ifdef LAPTOP
#    define F_HGHT 14
#    define F_WDTH 7
#  else
#    define F_HGHT 22
#    define F_WDTH 13
//#    define F_HGHT 14
//#    define F_WDTH  7
#  endif
#  define MAX_COLOR_NO 256
#  ifndef COLOR256
#    define MAX_PALETTE 16
#    define RAINBOW(x) gray[capd::min(15,capd::max(2,(int)(2+(1.-x)*14)))]
#  else
//#    define MAX_PALETTE 216
#    define MAX_PALETTE 316
#    define GRAY(x) capd::min(315,capd::max(216,(int)(216+(1.-x)*100.)))
#    define RAINBOW(x) capd::min(215,capd::max(16,(int)(16+(1.-x)*200)))
#  endif
#  define main mainEntry
#  define LineTo(i,j) MWLineTo(i,j)

#  define mlalloc malloc
#  define lfree free
#  define SYSTEM "WINDOWS 95"

#  define TAB_KEY 9

#  include <cstdarg>
#  include <stdio.h>
#  include <time.h>
#if defined(BORLAND)
#  include <alloc.h>
#endif
#  include <conio.h>
#  define HDR 800
#  define VDR 600
#  define HG

#  define var_head void *

#  define SC(c,r,g,b) red_c[c]=(BYTE)(255*(r));green_c[c]=(BYTE)(255*(g));blue_c[c]=(BYTE)(255*(b));
#  define COLOR(a) RGB(red_c[a],green_c[a],blue_c[a])
#  define mlalloc malloc
#  define lfree free

#if(!defined(LEFT_TOP_X))
#define LEFT_TOP_X 0
#endif

#if(!defined(LEFT_TOP_Y))
#define LEFT_TOP_Y 0
#endif
