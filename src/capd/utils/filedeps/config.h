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

// Copyright (C) 1997-2008 by Pawel Pilarczyk.
//
// This file is part of the Homology Library.  This library is free software;
// you can redistribute it and/or modify it under the terms of the GNU
// General Public License as published by the Free Software Foundation;
// either version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this software; see the file "license.txt".  If not, write to the
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

// Started in 2002. Last revision: September 21, 2006.


#ifndef _CHOMP_SYSTEM_CONFIG_H_
#define _CHOMP_SYSTEM_CONFIG_H_


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


#endif // _CHOMP_SYSTEM_CONFIG_H_

/// @}

