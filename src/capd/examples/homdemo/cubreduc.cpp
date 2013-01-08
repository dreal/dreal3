/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubreduc.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on February 15, 2003. Last revision: August 14, 2003.

// Former name(s) of this program: cubdemo1.cpp (until November 11, 2003).


#include "capd/homology/homology.h"
#include "cubdemo.h"

#include <exception>
#include <cstdlib>
#include <new>
#include <iostream>
#include <fstream>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CUBREDUC, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: main.cub addition.cub [result.cub].\n\
This is a demonstration program which verifies if the addition to the\n\
given main set can be reduced towards the main set without any change\n\
in homology. The cubes that were not reduced are saved to the result.\n\
Note that it can happen that the homology of the main set does not\n\
change, but the program is unable to reduce the added cubes.\n\
Optional arguments:\n\
-v N - version of reduction: 0 or 1.\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// ---------------------- DEMO ----------------------
// --------------------------------------------------

void demo (char *Xname, char *Aname, char *Yname, int version)
{
	// read the first set of cubes
	cubes X;
	readelements (Xname, X, "X");

	// read the second set of cubes if any
	cubes A;
	readelements (Aname, A, "A");

	// verify that the sets are disjoint
	for (int_t i = 0; i < A. size (); i ++)
	{
		const cube &q = A [i];
		if (X. check (q))
			throw "The sets are not disjoint.";
	}

	// compute the union of the two sets
	cubes both = X;
	both. add (A);

	// if both sets are empty, then this is wrong
	if (both. empty ())
		throw "Both sets are empty.";

	// determine the dimension of the cubes
	int dim = both [0]. dim ();

	// verify that all the cubes are of the same dimension
	for (int_t i = 0; i < both. size (); i ++)
		if (both [i]. dim () != dim)
			throw "Some cubes are of different dimension.";

	// allocate bitfields and display an appropriate message
	knownbits [dim];

	// reduce the union of the sets while keeping cubes which are in X
	sout << "Reducing the cubes... ";
	int_t prev = both. size ();

	if (version == 0)
	{
		cubes empty;
		cubreduce (both, empty, X);
	}
	else
	{
		while (1)
		{
			bool changed = false;
			for (int_t i = 0; i < A. size (); ++ i)
			{
				if (acyclic (A [i], both))
				{
					changed = true;
					both. remove (A [i]);
					A. removenum (i);
					-- i;
				}
			}
			if (!changed)
				break;
		}
	}

	sout << (prev - both. size ()) << " cubes removed.\n";

	// prepare a set for the non-reduced cubes
	cubes Y (both);
	Y. remove (X);

	// display the result of the reduction
	sout << "There are " << Y. size () << " cubes "
		"that could not be reduced.\n";

	// save the result to a file if requested to
	if (!Yname)
		return;
	sout << "Writing the result to '" << Yname << "'... ";
	std::ofstream out (Yname);
	if (!out)
		fileerror (Yname, "create");
	out << Y;
	sout << Y. size () << " cubes saved.\n";

	return;
} /* demo */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *Xname = NULL, *Aname = NULL, *Yname = NULL;
	int version = 0;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, Xname);
	arg (a, NULL, Aname);
	arg (a, NULL, Yname);
	arg (a, "v", version);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// if there are not enough file names, help should be displayed
	if (!Xname || !Aname)
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

	// set an appropriate program time message
	program_time = "Aborted after:";

	// try running the main function and catch an error message if thrown
	try
	{
		demo (Xname, Aname, Yname, version);
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

	// set an appropriate program time message
	program_time = "Total time used:";
	return 0;
} /* main */

/// @}

