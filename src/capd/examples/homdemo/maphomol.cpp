/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file maphomol.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on September 6, 2003. Last revision: November 30, 2004.

// Former name(s) of this program: mapdemo1.cpp (until November 11, 2003).


#include "capd/homology/homology.h"
#include "cubdemo.h"

#include <exception>
#include <new>
#include <iostream>
#include <fstream>
#include <cstdlib>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
MAPHOMOL, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: F.map X.cub A.cub Y.cub B.cub.\n\
This is a demonstration program which computes the homomorphism induced\n\
in homology by the given combinatorial cubical multivalued map.\n\
Optional arguments:\n\
-p p - compute the homology over Z modulo p instead of plain Z,\n\
-i - compose the map with the inverse of the homom. ind. by the inclusion,\n\
-g - compute homology generators (note: less effective reduction),\n\
-a - do the reductions carefully to prevent from spoiling acyclicity,\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// ---------------------- DEMO ----------------------
// --------------------------------------------------

void demo (char *Fname, char *Xname, char *Aname, char *Yname, char *Bname,
	bool inclusion, bool checkacyclic, int p, bool generators)
{
	// add an empty line for clearer output
	sout << '\n';

	// set the requested ring of coefficients if different from Z
	if (p > 0)
		integer::initialize (p);

	// read the sets from the input files
	CombinatorialMultivaluedMap Fcubmap;
	SetOfCubes Xcubes, Acubes, Ycubes, Bcubes;
	readelements (Xname, Xcubes, "X");
	readelements (Aname, Acubes, "A");
	readelements (Yname, Ycubes, "Y");
	readelements (Bname, Bcubes, "B");
	readmap (Fname, Fcubmap, "F");

	// compute the homology of the map
	Chain *hom_cx = NULL, *hom_cy = NULL;
	int maxlevel_cx, maxlevel_cy;
	ChainMap *hom_f = NULL;
	Chain **gen_cx, **gen_cy;
	CubicalComplex *gcompl_cx, *gcompl_cy;
	int maxlevel = Homology (Fcubmap, Xcubes, Acubes, Ycubes, Bcubes,
		hom_cx, maxlevel_cx, hom_cy, maxlevel_cy, hom_f,
		inclusion, checkacyclic ? 0x03 : 0x01,
		(generators && !inclusion) ? &gen_cx : NULL,
		(generators && !inclusion) ? &gcompl_cx : NULL,
		generators ? &gen_cy : NULL, generators ? &gcompl_cy : NULL);

	// add an empty line for clearer output
	sout << '\n';

	// if there was an error or the result is trivial, say it
	if (!hom_f || (maxlevel < 0))
	{
		sout << "The result is trivial or an error occurred.\n";
		return;
	}

	// show the computed homology to confirm the results
	sout << "The homology of the graph of F, same as of (X,A), "
		"is as follows:\n";
	ShowHomology (hom_cx, maxlevel_cx);

	sout << "The homology of (Y,B) is as follows:\n";
	ShowHomology (hom_cy, maxlevel_cy);

	sout << "The map induced in homology by F is as follows:\n";
	ShowHomology (*hom_f);

	// show the generators of homology of the graph and release the data
	if (generators && !inclusion && (maxlevel >= 0))
	{
		sout << "The computed homology generators of the graph of F "
			"are as follows:\n";
		ShowGenerators (gen_cx, hom_cx, maxlevel_cx, *gcompl_cx);
		delete gcompl_cx;
		for (int q = 0; q <= maxlevel_cx; q ++)
			delete [] (gen_cx [q]);
		delete gen_cx;
	}

	// show the generators of homology of Y and release the data
	if (generators && (maxlevel >= 0))
	{
		sout << "The computed homology generators of (Y,B) "
			"are as follows:\n";
		ShowGenerators (gen_cy, hom_cy, maxlevel_cy, *gcompl_cy);
		delete gcompl_cy;
		for (int q = 0; q <= maxlevel_cy; q ++)
			delete [] (gen_cy [q]);
		delete gen_cy;
	}

	// release the memory and finish
	if (hom_cx)
		delete [] hom_cx;
	if (hom_cy)
		delete [] hom_cy;
	if (hom_f)
		delete hom_f;

	return;
} /* demo */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *Fname = NULL, *Xname = NULL, *Aname = NULL,
		*Yname = NULL, *Bname = NULL;
	bool inclusion = false, checkacyclic = false;
	int p = 0;
	bool generators = false;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, Fname);
	arg (a, NULL, Xname);
	arg (a, NULL, Aname);
	arg (a, NULL, Yname);
	arg (a, NULL, Bname);
	arg (a, "p", p);
	argswitch (a, "g", generators, true);
	argswitch (a, "i", inclusion, true);
	argswitch (a, "a", checkacyclic, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// if there are not enough file names, help should be displayed
	if (!Bname)
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
		demo (Fname, Xname, Aname, Yname, Bname,
			inclusion, checkacyclic, p, generators);

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

