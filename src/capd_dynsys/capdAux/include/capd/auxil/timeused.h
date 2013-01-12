/// @addtogroup system
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file timeused.h
///
/// This file defines a simple data structure which can be used
/// to measure time used by the program (or some program parts)
/// and to display this time in a nice text format.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// You may want to include "textfile.h" before this file.
// Started on March 23, 2002. Last revision: February 9, 2003.

// NOTE: If you do not want to control the time measurement, but only want
// to make your program display a "Time used" message at its termination,
// then it is enough that you only link your program with "timeused.cpp"
// without even including this header file in your code.


#ifndef _CAPD_AUXIL_TIMEUSED_H_
#define _CAPD_AUXIL_TIMEUSED_H_

#include "capd/auxil/config.h"

#include <ctime>
#include <iostream>

namespace capd {
namespace auxil {


// classes defined within this header file:
class timeused;


// --------------------------------------------------
// ------------------- TIMEUSED ---------------------
// --------------------------------------------------

/// A class that stores the time at which it was initialized and then
/// returns or displays the time used since the initialization.
/// It displays this time when the destructor is invoked, e.g., at the end
/// of program run. This class is used in most of the CHomP programs
/// to measure the time used for the computations.
class timeused
{
public:
	/// The default constructor. It may be given a message
	/// to be displayed when the destructor is called.
	timeused (const char *msg = NULL);
	timeused (std::ostream &out, const char *msg = NULL);

	/// The destructor.
	~timeused ();

	/// Defines an output stream for displaying program's
	/// running time at program's termination.
	timeused &operator = (std::ostream &out);

	#ifdef OUTPUTSTREAM
	/// Defines an output stream for displaying program's
	/// running time at program's termination to a pair of streams.
	timeused &operator = (outputstream &out);
	#endif

	/// Turns off writing program's running time at program's
	/// termination by assigning 0 to an object of this class.
	timeused &operator = (int n);

	/// Changes the message displayed at program's termination.
	timeused &operator = (const char *msg);

	/// Reset the timer to the current moment.
	timeused &reset ();

	/// Returns the time from the initialization measured in seconds.
	operator double ();

	/// Shows the time used from the beginning up to the current point.
	/// The time is preceded with the message (default: "Time used").
	void show (std::ostream &out, const char *message = NULL) const;

	/// Shows the time used from the beginning up to the current point
	/// to the standard output stream.
	/// The time is preceded with the message (default: "Time used").
	void show (const char *message = NULL) const;

	/// Shows the time elapsed up to this point.
	friend std::ostream &operator << (std::ostream &out,
		const timeused &t);

protected:
	/// CPU usage start time (in seconds).
	double cpu0;
	
	/// Start time (in seconds).
	std::time_t t0;

	/// Output stream 1 (0 for no output).
	std::ostream *outstream1;

	/// Output stream 2 (0 for no output).
	std::ostream *outstream2;

	/// A message to display instead of "Used time" (if not 0).
	const char *message;

	/// Should the destructor display the time?
	/// Note: -1 makes the destructor display times only > 1 sec.
	int display;

}; /* timeused */

// --------------------------------------------------

inline timeused::timeused (const char *msg)
{
	reset ();
	outstream1 = NULL;
	outstream2 = NULL;
	message = msg;
	display = -1;
	return;
} /* timeused::timeused */

inline timeused::timeused (std::ostream &out, const char *msg)
{
	reset ();
	outstream1 = &out;
	outstream2 = NULL;
	message = msg;
	display = -1;
	return;
} /* timeused::timeused */

inline void timeused::show (std::ostream &out, const char *msg) const
{
	if (!msg)
		msg = message;
	if (!msg)
		msg = "Time used:";

	out << msg << ' ' << *this << '.' << std::endl;

	return;
} /* timeused::show */

inline timeused::~timeused ()
{
	if (!display || (!outstream1 && !outstream2))
		return;
	if ((display > 0) || (double (*this) > 1))
	{
		if (outstream1)
			show (*outstream1);
		if (outstream2)
			show (*outstream2);
	}
	return;
} /* timeused::~timeused */

inline timeused &timeused::operator = (std::ostream &out)
{
	outstream1 = &out;
	outstream2 = NULL;
	return *this;
} /* timeused::operator = */

#ifdef CAPD_OUTPUTSTREAM
inline timeused &timeused::operator = (outputstream &out)
{
	if (out. show)
		outstream1 = &(out. out);
	else
		outstream1 = NULL;
	if (out. log)
		outstream2 = out. getlogstream ();
	else
		outstream2 = NULL;
	return *this;
} /* operator = */
#endif

inline timeused &timeused::operator = (int n)
{
	display = n;
	return *this;
} /* timeused::operator = */

inline timeused &timeused::operator = (const char *msg)
{
	message = msg;
	return *this;
} /* timeused::operator = */

inline void timeused::show (const char *msg) const
{
	if (outstream1)
		show (*outstream1, msg);
	if (outstream2)
		show (*outstream2, msg);
	return;
} /* timeused::show */

// --------------------------------------------------

#ifndef CAPD_TIMEUSED
/// This symbol is defined if the "timeused" class is available,
/// and the variable "program_time" is defined.
#define CAPD_TIMEUSED
#endif

/// The external variable which measures the time used by the program
/// from its start. Note that in the destructor of this variable,
/// a message is displayed to std::cout indicating how much time
/// was used by the program in its entire run.
extern timeused program_time;


} // namespace auxil
} // namespace capd

#endif // _CAPD_AUXIL_TIMEUSED_H_

/// @}

