/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file kernel.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#define _low_level_
#include "capd/krak/hardware.h"
#include "capd/krak/kernel.h"


// platform-independent kernel implementation with wxWindows (wxWidgets)
#ifdef WXWIN
#  include "../src/capd/krak/wxWin.c"


#else // ******************************************************** wxWin *****


// kernel implementation for PC under DOS
#ifdef DOS
#  include "../src/capd/krak/ms-dos.c"
#endif

// kernel implementation for PC running 16 bits Windows, i.e. WINDOWS 3.1
#ifdef WIN31
#  include "../src/capd/krak/ms-win31.c"
#endif

// needed if running on PC with DOS or 16 bits WINDOWS
#ifdef DOS16
#  include "../src/capd/krak/dos16.c"
#endif

// kernel implementation for PC running 32 bits Windows, i.e. WINDOWS 95
#ifdef WIN95
#  include "../src/capd/krak/ms-win95.c"
#endif

// kernel implementation for X Windows on SUN 
#ifdef SUN_OS
#  include "../src/capd/krak/sun-os.c"
#endif

// kernel implementation for X Windows on PC under LINUX 
#ifdef LINUX
#  include "../src/capd/krak/linux.c"
#endif

// ####### Some old and rarely used kernel implementations ##########

#ifdef SUN_V
#  include "../src/capd/krak/sun_v.c"
#endif

#ifdef UNIX_CH
#   define UNIX_TXT
#   include "../src/capd/krak/unix_ch.c"
#endif

#ifdef MAC
#  include "../src/capd/krak/appl-mac.c"
#endif

#ifdef IBM_CH
#  include "../src/capd/krak/ms-dosch.c"
#endif


#endif // ******************************************************* wxWin *****

/// @}
