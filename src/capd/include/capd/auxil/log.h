/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file log.h
///
/// File contains functions and macro definitions for logging support
/// All log  informations can be easilly switched on/of by
/// defining  CAPD_LOG_ON  symbol before including log.h header.
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

//#ifndef _CAPD_AUXIL_LOG_H_
//#define _CAPD_AUXIL_LOG_H_
#include <iostream>
namespace capd{
/// Auxiliary functions and classes
namespace auxil{

#define CAPD_LOG_LEVEL 0

#define LOGGER std::cout

#undef LOG
#undef LOGLN
#undef CLOG

#if(defined(CAPD_LOG_ON))
/// LOGs to stream command name, execute it and prints its output
/// EXAMPLE:   for :        std::cout << LOG(5+6);
///            result is :  5+6 = 11
#define LOG(v) " " << #v <<" = " << v

/// LOGLN  in addition to LOG adds new line and the end.
#define LOGLN(v) LOG(v) << "\n"

/// uses LOGLN to log to standard stream cout.
#define CLOG(v) std::cout << LOGLN(v)
#else
#define LOG(v) ""
#define LOGLN(v) ""
#define CLOG(v) std::cout << ""
#endif


}}


//#endif /* _CAPD_AUXIL_LOG_H_ */
