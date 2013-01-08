/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file krakSetting.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// ################### Settings for the krak package ###################
// This file controls the setting in which the krak package is compiled.


#ifndef _CAPD_KRAK_KRAKSETTING_H_ 
#define _CAPD_KRAK_KRAKSETTING_H_ 

// This allows automatic detection of operating system and compiler
#include "capd/capd/operatingSystemSetting.h"
#include "capd/capd/compilerSetting.h"



/* If you wish just main() instead of int main(int argc, char* argv[])
   under Win95 or when using wxWidgets uncomment the following.
   This is needed because in the above cases main is actually redefined
   to mainEntry (Mainly used in krak_edu to avoid unnecessary warnings) */

//#define NO_CMD_LINE_ARGS

// Choose between color and black/white output
#if !defined (COLOR256) && !defined (BLACKWHITE)
#define COLOR256
//#define BLACKWHITE
#endif

// Comment out the following if you want the screen refreshing turned off
// for faster output. This has effect only under WIN95 or if using wxWidgets.
#define _REFRESH_

// Uncomment these lines if you want to change the location of the top
// upper corner of the graphics window.
//#define LEFT_TOP_X 10
//#define LEFT_TOP_Y 10


// Automatic detection of wxWindows (wxWidgets).
// Comment the middle #define out if you don't want to use wxWidgets.
#if defined (__WXMSW__) || defined (__WXGTK__) || defined (__WXMOTIF__) || \
 defined (__WXX11__) || defined (__WXMAC__) || defined (__WXUNIVERSAL__)
#define WXWIN
#endif

#endif // _CAPD_KRAK_KRAKSETTING_H_ 

/// @}
