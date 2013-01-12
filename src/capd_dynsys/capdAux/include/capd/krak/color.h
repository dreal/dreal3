
/////////////////////////////////////////////////////////////////////////////
/// @file color.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_COLOR_H_ 
#define _CAPD_KRAK_COLOR_H_ 

/// @addtogroup krak
/// @{

#define WHITE       0
#define BLACK       1
#define RED         2
#define GREEN       3
#define BLUE        4
#define YELLOW      5
#define MAGENTA     6
#define CYAN        7
#define ORANGE      8
#define VIOLET      9
#define PINE       10
#define BROWN      11
#define OLIVE      12
#define DARKBLUE   13
#define ORANGERED  14
#define BLUEGREEN  15

#define FRAME_FG   -1
#define FRAME_BG   -2

/// @}

namespace capd{
namespace krak{
   void set_colors(void);
}}

#endif // _CAPD_KRAK_COLOR_H_ 


