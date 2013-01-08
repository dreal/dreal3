/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file simbetti.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on September 4, 2003. Last revision: September 8, 2003.

// Former name(s) of this program: simdemo2.cpp (until November 11, 2003).


#include "capd/homology/homology.h"

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
SIMBETTI, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: file1.sim [file2.sim].\n\
This is a demonstration program which computes the Betti numbers\n\
of a given simplicial complex or a pair of simplicial complexes.\n\
Optional arguments:\n\
-p p - compute the homology over Z modulo p instead of Z,\n\
-g - compute and show homology generators,\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// ---------------------- DEMO ----------------------
// --------------------------------------------------

void demo (char *Xname, char *Aname, int p, bool generators)
{
	// add an empty line for clearer output
	sout << '\n';

	// set the requested ring of coefficients if different from Z
	if (p > 0)
		integer::initialize (p);

	// read the sets from the input files
	SimplicialComplex X, A;
	readcells (Xname, X, "X");
	readcells (Aname, A, "A");

	// compute the homology of the pair
	Chain *hom;
	Chain **gen;
	int maxlevel = Homology (X, "X", A, "A", hom,
		generators ? &gen : NULL);

	// show the computed homology to confirm the result
	ShowHomology (hom, maxlevel);

	// add an empty line for clearer output
	sout << '\n';

	// show the generators of homology and release the data
	if (generators && (maxlevel >= 0))
	{
		sout << "The computed homology generators are as follows:\n";
		ShowGenerators (gen, hom, maxlevel, X);
		for (int q = 0; q <= maxlevel; q ++)
			delete [] (gen [q]);
		delete [] gen;
	}

	// show Betti numbers
	if (maxlevel < 0)
		sout << "All the Betti numbers are zero.\n\n";
	else
	{
		sout << "The computed Betti numbers are:";
		for (int i = 0; i <= maxlevel; i ++)
			sout << ' ' << BettiNumber (hom [i]);
		sout << ".\nAll the remaining Betti numbers are zero.\n\n";
	}

	// release the allocated data from memory and finish
	if (hom)
		delete [] hom;
	return;
} /* demo */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *Xname = NULL, *Aname = NULL;
	int p = 0;
	bool generators = false;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, Xname);
	arg (a, NULL, Aname);
	arg (a, "p", p);
	argswitch (a, "g", generators, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// if there are not enough file names, help should be displayed
	if (!Xname)
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
		program_time = 1;

		// run the main procedure
		demo (Xname, Aname, p, generators);

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

