/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubsetdemo.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// This file copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on September 11, 2006. Last revision: July 27, 2007.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
using namespace capd::homology;
#include "capd/homengin/cubiset.h"

#include <iostream>
#include <exception>


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
HOM DEMO, ver. 0.01. Copyright (C) 2006 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
This is a demonstration program which performs a few simple operations\n\
on some cubical sets, and computes the homology of a cubical set.\n\
Call with -q for quiet operation.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// ---------------------- DEMO ----------------------
// --------------------------------------------------

static void Demo (bool quiet)
{
	// create an empty cubical set
	int left_coords [] = {0, 0, 0};
	int right_coords [] = {6, 6, 6};
	CubicalSet Q (left_coords, right_coords, 3);

	// add cubes to the cubical set
	int cube [] = {1, 0, 0};
	for (int i = 0; i < 3; ++ i)
	{
		cube [0] = i;
		for (int j = 0; j < 3; ++ j)
		{
			cube [1] = j;
			for (int k = 0; k < 5; ++ k)
			{
				cube [2] = k;
				Q. Add (cube);
			}
		}
	}

	// remove some cubes from the cubical set
	int hole [] = {1, 1, 1};
	Q. Delete (hole);
	hole [2] = 3;
	Q. Delete (hole);

	// compute the Betti numbers of the cubical set
	int Betti [4];
	ComputeBettiNumbers (Q, Betti, "PP", quiet);
	for (int i = 0; i < 4; ++ i)
		sout << (i ? ", " : "Betti numbers: ") << Betti [i];
	sout << ".\n";
	sout << "----------------------------------\n";
	
	// compute the Betti numbers again using the default engine
	int Betti2 [4];
	ComputeBettiNumbers (Q, Betti2, 0, quiet);
	bool wrongresult = false;
	for (int i = 0; i < 4; ++ i)
		if (Betti [i] != Betti2 [i])
			wrongresult = true;
	if (wrongresult)
		sout << "WARNING: The computations went wrong!\n";

	return;
} /* KleinBottle */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	bool quiet = false;

	// define the command-line options and switches
	arguments a;
	argswitch (a, "q", quiet, true);
	arghelp (a);

	// interprete the command-line arguments
	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

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
		Demo (quiet);

		// set an appropriate program time message and turn it on
		program_time = "Total time used:";
		program_time = 1;

		// finalize
		return 0;
	}
	catch (const char *msg)
	{
		sout << "ERROR: " << msg << '\n';
		return -1;
	}
	catch (const std::bad_alloc)
	{
		serr << "SORRY: Not enough memory.\n";
		return -1;
	}
	catch (const std::exception &err)
	{
		serr << "ERROR: " << err. what () << '\n';
		return -1;
	}
	catch (...)
	{
		sout << "ABORT: An unknown error occurred.\n";
		return -1;
	}
} /* main */

/// @}

