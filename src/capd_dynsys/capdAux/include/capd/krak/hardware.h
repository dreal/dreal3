/////////////////////////////////////////////////////////////////////////////
/// @file hardware.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* look for defines also at the compiler options */
#ifndef _CAPD_KRAK_HARDWARE_H_ 
#define _CAPD_KRAK_HARDWARE_H_ 

#include "capd/krak/krakSetting.h"

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <fstream>
#include <ctype.h>
#include <memory>
#include <sstream>

#if defined(WIN95) // mingw, visual and borland have this include header
#  include <conio.h>
#endif

#ifdef DOS
  #include "capd/krak/ms-dos.h"
#endif

#ifdef WIN95
  #include "capd/krak/ms-win95.h"
#endif

#ifdef SUN_OS
#  include "capd/krak/sun-os.h"
#endif

#ifdef MAC
  #include "capd/krak/appl-mac.h"
#endif





#ifdef SUN_V
#  define UNIX
#  define VIRT_MON
#  define SYSTEM "SUN_OS Solaris (VIRT)"
#endif

#ifdef UNIX_CH
#  include "capd/krak/unix-ch.h"
#endif

#ifdef LINUX
#  include "capd/krak/linux.h"
#endif

#ifdef DOS16
#  include "capd/krak/dos16.h"
#endif

#ifdef UNIX
#  include "capd/krak/unix.h"
#endif

#ifdef VIRT_MON
#  include "capd/krak/virt-mon.h"
#endif

#ifdef WIN31 // Is it only for WIN 3.1? What about Win95?
#  define PATTWORD int
#else
#  define PATTWORD unsigned char
#endif

#ifdef WXWIN
#  include "capd/krak/wxWin.h"
#endif

#ifndef SYSTEM
#  define  SYSTEM unknown
#endif


#endif // _CAPD_KRAK_HARDWARE_H_ 
