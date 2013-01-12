/// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file compilerSetting.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// This file controls the compiler setting in which the krak, interval
// and possibly also other packages of capd are compiled.
//
// Note that you don't have to modify this file - most settings can be
// selected with the -D argument of your command-line compiler
// or in your project. However, if the auto-detection does not work
// in your case, you may want to modify some specific options.


#ifndef _CAPD_CAPD_COMPILERSETTING_H_ 
#define _CAPD_CAPD_COMPILERSETTING_H_ 


// ################# Manual compiler selection for MS-Windows ############
// Uncomment exactly one line of the following if the automatic settings
// don't work for you. Note that if the compilation is not under MS Win,
// all these settings should be commented-out.
//#define GCC_MS_WIN   // gcc compiler for MS Win (e.g., MinGW or Dev-Cpp)
//#define VISUAL       // Visual C++ compiler
//#define BORLAND      // Borland compiler



// ################# Automatic compiler selection for MS-Windows ############
// Determine which compiler is being used. Note that the code in the
// entire package relies on the settings like BORLAND, VISUAL, etc.,
// and not the ones that are used here for the auto-detection.

// auto-detect only if not set before
#if !defined (BORLAND) && !defined (VISUAL) && !defined (GCC_MS_WIN)

// Is the GNU C++ compiler for MS Windows being used?
// (most likely MinGW, for instance the one bundled with DevCpp)
#if (defined (__WIN32__) && defined (__GNUC__)) || defined (__MINGW32__)
#  define GCC_MS_WIN

// Is the Borland compiler being used?
#elif defined (__BORLANDC__)
#  define BORLAND

// Is the Microsoft Visual C++ compiler being used?
#elif defined (_MSC_VER)
#  define VISUAL
#endif

#endif // automatic compiler selection

#endif // _CAPD_CAPD_COMPILERSETTING_H_ 

/// @}
