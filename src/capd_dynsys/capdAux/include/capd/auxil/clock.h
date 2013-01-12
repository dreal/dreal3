/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file clock.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_AUXIL_CLOCK_H_ 
#define _CAPD_AUXIL_CLOCK_H_ 
#include "capd/settings/operatingSystemSetting.h"
  #if defined (LINUX) || defined (SUN_OS)
  // ************************************************ //
    //#define _Clock_h_
    #include <sys/time.h>
    #include <sys/times.h>

    // world time in seconds as a long double
    inline long double getWorldSeconds(){
      struct timeval buffer;
      struct timezone tz;
      gettimeofday(&buffer,&tz);
      return (long double)(buffer.tv_sec)+(long double)(buffer.tv_usec)/1000000;
    }

    inline double getProcessInstructionSeconds(){
      struct tms buffer;
      // buffer.tms_utime - clock ticks used by process instructions
      // buffer.tms_stime - clock ticks used for process by system

      // process instructions time in seconds as a double
      times(&buffer);
      return ((double)(buffer.tms_utime)/CLOCKS_PER_SEC);
    }

  // ************************************************ //
  #else
  // ************************************************ //
    #include <time.h>
    #include <sys/types.h>
    #include <sys/timeb.h>

    // ************************************************ //

    // world time in seconds as a long double
    inline long double  getWorldSeconds(){
      struct /*_*/_timeb/*64*/ timebuffer;  // 64 version needed after year 2037, it requires newer versions of msvcrt.dll (6.10 or higher).
      _ftime/*64*/(&timebuffer);
      return double(timebuffer.time)+timebuffer.millitm/1000.;
    }

  // ************************************************ //
  #endif

  /* Function getProcessSeconds returns process time in seconds as a double */
  /* compatibility: Windows/Unix */
  inline double getProcessSeconds(){
    return (double)clock()/CLOCKS_PER_SEC;
  }

  /* Obsolete name for getProcessSeconds above */
  /* compatibility: Windows/Unix */
  inline double Clock(){
    return (double)clock()/CLOCKS_PER_SEC;
  }

#endif // _CAPD_AUXIL_CLOCK_H_ 


/// @}

