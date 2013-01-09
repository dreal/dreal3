/// @addtogroup system
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file config.h
///
/// This file contains some precompiler definitions which indicate
/// the operating system and/or compiler used. Most definitions usually
/// should be provided in the command line of the compiler, but if none
/// are given then some reasonable values are determined based on the
/// definitions already provided by the compiler (GNU C++ is supported).
/// 
/// The first section determines the operating system choice:
/// either Unix-like, or DOS/Windows-like.
/// It defines ppDOS for opening binary files with the "ios::binary" flag
/// and other features available only in DOS/Windows.
/// It defines ppUNIX to activate Unix-characteristic behavior of programs,
/// and to suppress functions inavailable under Unix.
/// It defines both for the GNU C++ compiler used in DOS/Windows.
///
/// Then it determines whether the wxWindows (wxWidgets) GUI is available,
/// based on one of the various symbols defined by the wx-config script.
/// If so, then the symbol ppWXWIN is defined.
///
/// Eventually, the type to be used as 16-bit integers and 32-bit integers
/// is defined.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in 2002. Last revision: January 25, 2010.


#ifndef _CAPD_HOMOLOGY_CONFIG_H_ 
#define _CAPD_HOMOLOGY_CONFIG_H_ 


#if (defined (ppUNIX) || defined (ppDOS))
#elif ((defined __GNUC__) && (defined __WIN32__))
	/// Defines the system type as DOS/Windows-like.
	#define ppDOS
	/// Defines the system type as Unix-like.
	#define ppUNIX
#elif (defined (DJGPP) || defined (DEVCPP) || defined (MINGW))
	/// Defines the system type as DOS/Windows-like.
	#define ppDOS
	/// Defines the system type as Unix-like.
	#define ppUNIX
#elif (defined (_BORLANDC_) || defined (__BORLANDC__) || defined (_MSC_VER))
	/// Defines the system type as DOS/Windows-like.
	#define ppDOS
#else
	/// Defines the system type as Unix-like.
	#define ppUNIX
#endif



#if (defined (__WXMSW__) || defined (__WXGTK__) || defined (__WXMAC__) || \
	defined (__WXMOTIF__) || defined (__WXX11__))

	/// This system is defined iff the wxWidgets (wxWindows) library
	/// interface is available.
	#define ppWXWIN

#endif


#ifdef __LONG_MAX__
	/// Defines the type of 16-bit integers.
	typedef short int16;
	#if (__LONG_MAX__ > 2147483647)
		/// Defines the type of 32-bit integers.
		typedef int int32;
	#else
		/// Defines the type of 32-bit integers.
		typedef long int32;
	#endif
#else
	/// Defines the type of 16-bit integers.
	typedef short int16;
	/// Defines the type of 32-bit integers.
	typedef int int32;
#endif

/// Index type for indexing arrays, counting cubes, etc.
/// to be used in some core data structures.
/// Must be signed integer. Use a 32-bit type ("int" in most cases)
/// to minimise memory usage, and a 64-bit type (typically this
/// would be "long" if compiling a 64-bit program)
/// if you want to go beyond limitations that would not allow you
/// to use huge amounts of memory (but note that then the program
/// will be up to twice more memory consuming).
/// Please note that the software may not have been fully adjusted yet
/// to using a different type than "int" here, and thus may not work
/// if dealing with huge data.
typedef int int_t;


#endif // _CAPD_HOMOLOGY_CONFIG_H_ 

/// @}

