/////////////////////////////////////////////////////////////////////////////
/// @file IntervalSettings.h
///
/// Interval Arithmetics package settings file
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_INTERVAL_INTERVALSETTINGS_H_
#define _CAPD_INTERVAL_INTERVALSETTINGS_H_

//////////////////////////////////////////////////////////////////////////////////
// INTERVAL SETTINGS
//////////////////////////////////////////////////////////////////////////////////

/// the following option speed up computations but enlarge programm size
#define __INTERVAL_SPEED_OPTIMIZED__

/// uncomment the following line for the debugging mode
//#define  __DEBUGGING__

/// uncomment the following line if you want initialize intervals with 0
#define __INTERVAL_INIT_0__

/// uncomment the following line if you want to use deprecated interval functions
//#define __INTERVAL_DEPRECATED__


//////////////////////////////////////////////////////////////////////////////////
//     DO NOT CHANGE FOLLOWING LINES
//////////////////////////////////////////////////////////////////////////////////

#ifdef __INTERVAL_SPEED_OPTIMIZED__
#define __INLINE__ inline
#else
#define __INLINE__
#endif

#endif // _CAPD_INTERVAL_INTERVALSETTINGS_H_
