/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubinclu.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on July 2, 2003. Last revision: October 6, 2004.

// Former name(s) of this program: cubdemo3.cpp (until November 11, 2003).


#include "capd/homology/homology.h"
#include "cubdemo.h"

#include <exception>
#include <cstdlib>
#include <new>
#include <iostream>
#include <fstream>
#include <sstream>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CUBINCLU, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: X1.cub [...] Xn.cub <OR> -r X1.cub A1.cub [...] Xn.cub An.cub.\n\
This is a demonstration program which computes maps induced in homology\n\
by the inclusion maps of each set into the next one. In fact, each set\n\
X_k and/or A_k may only contain these cubes that should be added to the\n\
previous set. *** NOTE *** Relative homology support not implemented, yet.\n\
Optional arguments:\n\
-s - save the reduced sets to files (replace the input sets),\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";

// the maximal number of sets of cubes allowed
#define MAXSETS 256


// --------------------------------------------------
// ---------------------- DEMO ----------------------
// --------------------------------------------------

static void readcubicalsets (cubes Xcubes [], cubes Acubes [],
	char *filenames [], int n, bool relative)
{
	// verify if any of the sets is nonempty
	bool nonempty = false;

	// read the sets of cubes
	for (int i = 0; i < n; i ++)
	{
		// create a suitable name of the set
		std::ostringstream s;
		s << "X" << (i + 1);

		// read the cubes from the given file(s)
		readelements (filenames [relative ? 2 * i : i], Xcubes [i],
			s. str (). c_str ());

		// read the other set if relative homology is considered
		if (relative)
		{
			std::ostringstream s;
			s << "A" << (i + 1);
			readelements (filenames [2 * i + 1], Acubes [i],
				s. str (). c_str ());
		}

		// check if any of the sets is nonempty
		if (Xcubes [i]. size () || Acubes [i]. size ())
			nonempty = true;
	}

	// if the sets are empty, the result is trivial
	if (!nonempty)
		throw "All the sets are empty. The result is trivial.\n";

	return;
} /* readcubicalsets */

static void savecubicalsets (cubes Xcubes [], cubes Acubes [],
	char *filenames [], int n, bool relative)
{
	for (int i = 0; i < n; i ++)
	{
		// write the cubes to the given file(s) [replace old ones!!!]
		std::ofstream out (filenames [relative ? 2 * i : i]);
		if (!out)
			sout << "WARNING: Can't re-write '" <<
				filenames [relative ? 2 * i : i] <<
				"' with the result.\n";
		else
			out << "; Reduced set X" << (i + 1) <<
				" follows.\n" << Xcubes [i];
		if (relative)
		{
			std::ofstream out (filenames [2 * i + 1]);
			if (!out)
				sout << "WARNING: Can't re-write '" <<
					filenames [2 * i + 1] <<
					"' with the result.\n";
			else
				out << "; Reduced set A" << (i + 1) <<
					" follows.\n" << Acubes [i];
		}
	}

	return;
} /* savecubicalsets */

static void displayresults (chaincomplex<integer> *homology [],
	chainmap<integer> *inclusions [],
	multitable<cubicalcomplex> generators [], int n)
{
	// show the homology
	sout << "\n*** Computed Betti numbers follow ***\n\n";
	for (int k = 0; k < n; k ++)
	{
		sout << "For X" << (k + 1);
		for (int i = 0; i <= homology [k] -> dim (); i ++)
			sout << (i ? ", " : ": ") <<
				homology [k] -> getnumgen (i);
		sout << ".\n";
	}

	// show the inclusion maps
	sout << "\n*** Computed homomorphisms follow ***\n";
	for (int k = 0; k < (n - 1); k ++)
	{
		sout << "\nHomomorphism no. " << (k + 1) << ":\n";
		char xname [] = {"x"};
		char yname [] = {"y"};
		xname [0] = (char) ('a' + k);
		yname [0] = (char) ('b' + k);

		inclusions [k] -> show (sout, "\ti", xname, yname, NULL);
	}

	// show the homology generators
	sout << "\n*** Computed homology generators follow ***\n\n";
	for (int k = 0; k < n; k ++)
	{
		// say for which set the generators are displayed
		sout << "+++ Generators of X" << (k + 1) << " follow +++\n";

		// prepare a variable to store the number of the
		// first generator of the given dimension
		int startgen = 0;

		// display generators of each dimension separately
		for (int i = 0; i <= homology [k] -> dim (); i ++)
		{
			// determine the number of generators of this dim.
			int ngen = homology [k] -> getnumgen (i);

			// if there are no generators, skip this dimension
			if (!ngen)
				continue;

			// show all the generators of this dimension
			sout << "--- Dim " << i << ": " << ngen <<
				" generators ---\n";
			for (int j = 0; j < ngen; j ++)
				sout << generators [k] [startgen + j] <<
					'\n';

			// update the offset of generators for the next dim.
			startgen += ngen;
		}
	}

	return;
} /* displayresults */

static void demo (char *filenames [], int n, bool relative, bool savesets)
// This procedure is an interface for the main procedure in this example.
// Read sets of cubes from text files and then display the result.
{
	// prepare the data to process
	cubes Xcubes [MAXSETS], Acubes [MAXSETS];

	// read all the sets of cubes
	readcubicalsets (Xcubes, Acubes, filenames, n, relative);

	// reduce full-dimensional sets of cubes for inclusion computation
	ReduceFullDimCubes (Xcubes, Acubes, n);

	// save the reduced sets if requested to
	if (savesets)
		savecubicalsets (Xcubes, Acubes, filenames, n, relative);

	// prepare empty data structures for the result
	chaincomplex<integer> **homology;
	chainmap<integer> **inclusions;
	multitable<cubicalcomplex> generators [MAXSETS];

	// compute the homomorphisms induced by the inclusions in homology
	InclusionMapsHomology (Xcubes, Acubes, n, homology, inclusions,
		generators);

	// display the computed data
	displayresults (homology, inclusions, generators, n);

	// release allocated data
	for (int i = 0; i < n; i ++)
		delete homology [i];
	delete [] homology;
	for (int i = 0; i < n - 1; i ++)
		delete inclusions [i];
	delete [] inclusions;

	return;
} /* demo */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *filenames [MAXSETS];
	int n = 0;
	bool relative = false;
	bool savesets = false;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, filenames, n, MAXSETS);
	argswitch (a, "r", relative, true);
	argswitch (a, "s", savesets, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// adjust the number of sets if necessary
	if (relative)
		n /= 2;

	// warn the user against using relative homology
	if (relative)
		sout << "WARNING: Relative homology not implemented, yet!\n";

	// if there are not enough file names, help should be displayed
	if (!n)
		argresult = 1;

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested, show help information
	if (argresult > 0)
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		// set an appropriate program time message
		program_time = "Aborted after:";

		// run the main procedure
		demo (filenames, n, relative, savesets);

		// set an appropriate program time message
		program_time = "Total time used:";

		// finalize
		return 0;
	}
	catch (const char *msg)
	{
		sout << "ERROR: " << msg << '\n';
		return -1;
	}
	catch (const std::exception &e)
	{
		sout << "ERROR: " << e. what () << '\n';
		return -1;
	}
	catch (...)
	{
		sout << "ABORT: An unknown error occurred.\n";
		return -1;
	}
} /* main */

/// @}

