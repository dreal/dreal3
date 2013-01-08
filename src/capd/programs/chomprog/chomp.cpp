/////////////////////////////////////////////////////////////////////////////
/// @file chomp.cpp
///
/// @author Pawel Pilarczyk (this file)
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

// Started in March 2006. Last revision: July 26, 2007.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
#include "capd/homology/homtools.h"

#include <cstdlib>
#include <ctime>
#include <new>
#include <exception>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <sstream>

#include "capd/homengin/engines.h"
#include "capd/homengin/cubfiles.h"
#include "capd/homengin/algstruct.h"

using namespace capd::homology;
using namespace capd::homengin;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
This is CHomP, version 1.00 beta5, 07/26/07. Copyright (C) 1997-2007\n\
by William Kalies, Marian Mrozek, Pawel Pilarczyk, and others.\n\
This is free software. No warranty. Consult 'license.txt' for details.\n";

const char *helpinfo = "\
This program computes Betti numbers of a cubical set and writes them to\n\
the standard output (separated with spaces). Call this program with the\n\
name of a file that contains the cubical set:\n\n\
\tchomp filename.cub\n\n\
Call this program with --help for more information, or consult the\n\
Computational Homology Project website http://chomp.rutgers.edu/";

const char *longhelp = "\
This program computes the homology of a cubical set or relative homology\n\
of a pair of cubical sets. Please, consult the Computational Homology\n\
Project website at http://chomp.rutgers.edu/ for detailed description\n\
of this program and instructions on how to use it.\n\
Brief information on supported data formats and available options follows.\n\
\n=== Supported Data Formats ===\n\n\
The cubical sets can be defined either in a text file, or in a binary one.\n\
In the text mode, a full cube is defined by its vertex with minimal\n\
coordinates (x1,x2,...,xN); elementary cubes are defined as a pair of\n\
vertices: the minimal and the maximal one: [(x1,...,xN)(y1,...,yN)],\n\
or as a product of intervals [a1,b1]x...x[aN,bN].\n\
In the binary format, black pixels from Windows BMP files form\n\
2-dimensional full cubical sets, and the BMD format is used to define\n\
full cubical sets of dimension other than 2.\n\
The type of a file is recognized automatically using some heuristics.\n\
Call this program with the --files argument to see descriptions of\n\
all the supported file types.\n\
\n=== Homology Engines ===\n\n\
Several implementations of various algorithms can be used for the homology\n\
computation with this program. An optimal one is chosen based on the input\n\
data, but this is a heuristic choice which may not always be the best one.\n\
To force the usage of a specific algorithm, use the command-line option\n\
--engine (or -e) followed by the engine name. Call the program with the\n\
--engines switch to see the list of engines that are compiled-in.\n\
\n=== Other Options and Switches ===\n\n\
Additional command-line arguments recognized by the program are as follows:\n\
-b filename - save Betti numbers to a file (one number per line),\n\
-w n - wrap the space (repeat for each axis, use 0 for no space wrapping),\n\
--quiet - do not output any messages to the screen,\n\
--verbose (or -v) - show detailed information on the computations,\n\
--log file - log the verbose output to a file (actually, even more).\n";


// --------------------------------------------------
// --------------------- CHOMP ----------------------
// --------------------------------------------------

/// Runs the homology computation and displays the result.
int runchomp (const char *Xname, const char *Yname,
	const char *eng, const char *Bettiname,
	bool verbose, const int *wrap, bool wrapping)
{
	// turn off screen output unless verbose output requested
	if (!verbose)
	{
		sout. show = false;
		scon. show = false;
		fcout. turnOff ();
	}
	else
		fcout. turnOn ();

	// create wrappers for the files with sets of cubes
	cubfile *X = 0;
	if (Xname)
		X = cubtype::newfile (Xname);
	if (!X)
		throw "Unable to open the file with cubes.";
	int dim = X -> dim ();
	cubfile *Y = 0;
	if (Yname)
	{
		Y = cubtype::newfile (Yname);
		if (!Y)
			serr << "WARNING: Unable to open the second file. "
				"Ignoring it.\n";
	}

	// apply space wrapping if necessary
	if (X && wrapping)
		X -> setwrapping (wrap);
	if (Y && wrapping)
		Y -> setwrapping (wrap);

	// find the best engine to use for the homology computation
	const engine *e = eng ? engine::find (eng) : engine::find (X, Y);

	// indicate the time used so far
	sout << "Time used so far: " << program_time << ".\n";

	// compute the (relative) homology of the set(s) of cubes
	algstruct<capd::homology::integer> hom;
	if (!Y)
		e -> homology (*X, hom);
	else
		e -> homology (*X, *Y, hom);

	// show the result of the homology computation
	sout << "The computed homology is " << hom << ".\n";
	sout << "Betti numbers: ";
	if (!verbose)
		sout. show = true;
	for (int i = 0; i <= dim; ++ i)
		sout << (i ? " " : "") << hom. getBetti (i);
	sout << '\n';
	if (!verbose)
		sout. show = false;

	// save the Betti numbers to a file
	if (Bettiname && *Bettiname)
	{
		std::ofstream out (Bettiname);
		if (!out)
			fileerror (Bettiname, "create");
		for (int i = 0; i <= dim; ++ i)
			out << hom. getBetti (i) << '\n';
	}

	// delete the wrappers for the sets of cubes
	delete X;
	delete Y;
	return 0;
} /* runchomp */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

const int maxdim = 32;

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// turn off program time reporting
	program_time = 0;

	// prepare user-configurable data
	char *Xname = 0;
	char *Yname = 0;
	char *Bettiname = 0;
	char *engine = 0;
	int wrap [maxdim];
	for (int i = 0; i < maxdim; ++ i)
		wrap [i] = 0;
	int wrapcount = 0;
	bool showlonghelp = false;
	bool showengines = false;
	bool showfiles = false;
	bool verbose = false;

	// analyze the command line
	arguments a;
	arg (a, 0, Xname);
	arg (a, 0, Yname);
	arg (a, "b", Bettiname, "betti.txt");
	argswitch (a, "v", verbose, true);
	argswitch (a, "-verbose", verbose, true);
	arg (a, "w", wrap, wrapcount, maxdim);
	argswitch (a, "-files", showfiles, true);
	argswitch (a, "-engines", showengines, true);
	arg (a, "e", engine);
	arg (a, "-engine", engine);
	argswitch (a, "-help", showlonghelp, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's title
	if (argresult || (!argresult && verbose) || showlonghelp ||
		showfiles || showengines || !Xname)
		sout << title << '\n';

	// display help info if no file name is given
	if (!Xname)
		argresult = 1;

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if extended help requested, show it
	if (showlonghelp)
	{
		sout << longhelp << '\n';
		return 1;
	}
	
	// show file types or engines if requested to
	if (showfiles || showengines)
	{
		std::ostringstream s;
		if (showengines)
			engine::showlist (s);
		if (showengines && showfiles)
			s << "\n========================================"
				"=====================================\n\n";
		if (showfiles)
			cubtype::showlist (s);
		sout << s. str ();
		return 1;
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
		// copy the wrapping argument if only one specified
		if (wrapcount == 1)
		{
			for (int i = 1; i < maxdim; ++ i)
				wrap [i] = wrap [0];
		}

		// turn on an error time message
		program_time = "Aborted after";

		// run the computations
		runchomp (Xname, Yname, engine, Bettiname, verbose, wrap,
			wrapcount != 0);

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


// TODO: check messages & verbosity, handling empty sets, PP_BIN, BK bitcodes

