
/////////////////////////////////////////////////////////////////////////////
/// @file pattern.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _pattern_h_
//#include "capd/capd/myC.h"
#define _pattern_h_

#define MAX_PATTERN_NO 17

#define EMPTY_P     0
#define SOLID_P     1
#define HLINE_P     2
#define VLINE_P     3
#define DHLINE_P    4
#define DVLINE_P    5
#define DOT_P       6
#define DDOT_P      7
#define DUST_P      8
#define DDUST_P     9
#define SLASH_P    10
#define ISLASH_P   11
#define WHDLINE_P  12
#define DWHDLINE_P 13
#define HASH_P     14
#define DHASH_P    15
#define WHASH_P    16
#define DWHASH_P   17
#define WVLINE_P   18
#define VDOT_P     19

namespace capd{
namespace krak{
   extern PATTWORD *patt_pntr[];
}}
#endif
