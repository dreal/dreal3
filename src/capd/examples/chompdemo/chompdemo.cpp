/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file chompdemo.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// This file copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This program uses the CAPD and CHOMP libraries. It is free software;
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

// Started in March 2006. Last revision: April 12, 2006.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
using namespace capd::homology;

#include "capd/homengin/homology.h"


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CHomP DEMO, ver. 0.01. Copyright (C) 2006 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.\n";

const char *helpinfo = "\
This program computes Betti numbers of a cubical set contained in the\n\
program itself. You can select the engine to use as a command-line\n\
argument. Please, refer to the source code for further details.";


// --------------------------------------------------
// ------------------- CHOMP_DEMO -------------------
// --------------------------------------------------

/// Runs the homology computation and displays the result.
int chomp_demo (const char *engine = 0)
{
	// define a set of cubes
	const int dim = 3;
	int sizes [] = {64, 3, 3};
	char buffer [] = {
		'\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF',
		'\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\x00', '\xFF',
		'\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF',

		'\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF',
		'\xFF', '\x00', '\x00', '\xFF', '\xFF', '\xFF', '\x00', '\xFF',
		'\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF',

		'\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF',
		'\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\x00', '\xFF',
		'\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF', '\xFF',
	};

	// prepare a table for the Betti numbers
	int betti [dim + 1];

	// compute the Betti numbers
	bool quiet = false;
	int *wrapping = 0;
	ComputeBettiNumbers (buffer, sizes, dim, betti, engine,
		wrapping, quiet);

	// show the result of the homology computation
	sout << "Betti numbers: ";
	for (int i = 0; i <= dim; ++ i)
		sout << (i ? " " : "") << betti [i];
	sout << '\n';

	return 0;
} /* chomp_demo */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *eng = 0;

	// analyze the command line
	arguments a;
	arg (a, 0, eng);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's title
	sout << title << '\n';

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if (argresult > 0)
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	int result = 0;
	try
	{
		// turn on an error time message
		program_time = "Aborted after";

		// run the computations
		chomp_demo (eng);

		// show the time used for the computations
		sout << "Total time used: " << program_time << ".\n";
		program_time = 0;
	}
	catch (const char *msg)
	{
		serr << "ERROR: " << msg << '\n';
		result = -1;
	}
	catch (const std::string &str)
	{
		serr << "ERROR: " << str << '\n';
		result = -1;
	}
	catch (const std::bad_alloc)
	{
		serr << "SORRY: Not enough memory.\n";
		result = -1;
	}
	catch (const std::exception &err)
	{
		serr << "ERROR: " << err. what () << '\n';
		result = -1;
	}
	catch (...)
	{
		serr << "ABORT: An unknown error occurred.\n";
		result = -1;
	}

	return result;
} /* main */

/// @}

