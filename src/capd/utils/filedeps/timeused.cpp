/// @addtogroup system
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file timeused.cpp
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

// Started on March 23, 2002. Last revision: June 3, 2004.


#include "config.h"
#include "timeused.h"

#include <ctime>
#include <iostream>
#include <iomanip>

#ifdef ppUNIX
#include <sys/time.h>
#if ((!defined (ppDOS)) || defined (DJGPP))
#include <sys/resource.h>
#endif
#include <unistd.h>
#endif

namespace chomp {
namespace homology {


// --------------------------------------------------
// ------------------- TIMEUSED ---------------------
// --------------------------------------------------

inline double currentcpu ()
// Return the current time in seconds.
{
	#if ((!defined (ppDOS)) || defined (DJGPP))
	struct rusage usage;
	getrusage (RUSAGE_SELF, &usage);
	return usage. ru_utime. tv_sec + usage. ru_utime. tv_usec / 1e6 +
		usage. ru_stime. tv_sec + usage. ru_stime. tv_usec / 1e6;
	#else
	return (double) std::clock () / CLK_TCK;
	#endif
} /* currenttime */

inline std::ostream &showseconds (std::ostream &out, double seconds, int precision)
{
	int prec = out. precision ();
	out. setf (std::ios::fixed);

	out << std::setprecision (precision) << seconds << " sec";
//	if (seconds < 60);
	if (seconds < 3600)
		out << " (" << std::setprecision (precision + 1) <<
			(seconds / 60) << " min)";
	else
		out << " (" << std::setprecision (precision + 1) <<
			(seconds / 3600) << " hours)";

	out. unsetf (std::ios::fixed);
	out. precision (prec);

	return out;
} /* showseconds */

std::ostream &operator << (std::ostream &out, const timeused &t)
{
	double c_sec = currentcpu () - t. cpu0;
	std::time_t t1;
	std::time (&t1);
	double t_sec = std::difftime (t1, t. t0);

	int precision = 0;
	if (c_sec < 100)
		precision ++;
	if (c_sec < 10)
		precision ++;

	showseconds (out, c_sec, precision);

	if (t_sec > c_sec + 1)
	{
		out << " out of ";
		showseconds (out, t_sec, 0);
	}

	return out;
} /* operator << */

timeused &timeused::reset ()
{
	cpu0 = currentcpu ();
	std::time (&t0);
	return *this;
} /* timeused::reset */

timeused::operator double ()
{
	if (cpu0 >= 0)
		return (currentcpu () - cpu0);
	std::time_t t1;
	std::time (&t1);
	return std::difftime (t1, t0);
} /* timeused::operator double */

// --------------------------------------------------

timeused program_time (std::cout);


} // namespace homology
} // namespace chomp

/// @}

