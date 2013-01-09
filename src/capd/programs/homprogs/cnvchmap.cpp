/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cnvchmap.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on May 1, 1999. Last revision: May 5, 2000 (November 23, 2002).


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "cells.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

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
CNVCHMAP, ver. 0.06. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: Map.dat [-e] [-yCy.lst] Cx.chn [Cy.chn] Map.chm [-rX -rY] [-w]\n\
This program converts a chain map from the output format of 'chmap'\n\
by Marcin Mazur and Jacek Szybowski to the input format for 'homchain'.\n\
The space after '-y' is optional, it is there for your convenience.\n\
Parameters:\n\
-y  - read cells which generate Cy from the file whose name follows,\n\
-x  - read cells which generate Cx from the file whose name follows,\n\
-e  - the map is an endomorphism; omit 'Cy.chn' then.\n\
-r  - read the list of cubes which form the other pair element of the\n\
\tdomain for relative homology computation; for the range use '-r' again,\n\
-wn - use space wrapping every n; use for each axis separately,\n\
-h  - display this brief help information and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// -------------------- CNVCHMAP --------------------
// --------------------------------------------------

int analyzedimension (char *inputfilename)
// Analyzes what the dimension of the space is.
// Returns the dimension or error code: -1 = displayed, -2 = not displayed.
{
	textfile in;
	if (in. open (inputfilename) < 0)
	{
		sout << "Can't open the input file to analyze its " <<
			"dimension.\n";
		return -1;
	}

	// find the first occurence of an opening brace
	while ((in. checkchar () != '[') && (in. checkchar () != EOF))
		in. readchar ();
	if (in. checkchar () != '[')
		return -2;
	else
		in. readchar ();

	// read the opening parenthesis
	if (in. checkchar () != 40)
		return -2;
	in. readchar ();

	// read numbers and count how many of them are separated by commas
	int dim = 0;
	while ((in. checkchar () != EOF) && (in. checkchar () != 41))
	{
		in. readnumber (0, 1);
		dim ++;
	}

	return dim;
} /* analyze dimension */

int cnvchmap (char *inmapfilename,
	char *incxfilename, char *incyfilename,
	char *outcxfilename, char *outcyfilename, char *outmapfilename,
	char *relXfilename, char *relYfilename, int endomorphism)
// Convert a chain map given in the input file, with optional Cy file name.
// Write output to files whose names are given.
{
	// determine the dimension of the space
	int maxdim = analyzedimension (inmapfilename);
	int cydim = (incyfilename) ? analyzedimension (incyfilename) :
		maxdim;
	if ((maxdim <= 0) || (cydim <= 0))
	{
		if (maxdim < -1)
			sout << "Can't determine the dimension " <<
				"of the space.\n";
		return -1;
	}
	if (maxdim != cydim)
		sout << "WARNING: Diffrent space dimensions " <<
			"in Cx and Cy.\n";
	if (maxdim < cydim)
		maxdim = cydim;

	// set the dimension of points
	point::spacedimension (maxdim);

	// prepare two cell complexes
	cellcomplex cx, cy;

	// read Cx from an input file if required
	if (incxfilename && *incxfilename)
	{
		sout << "Reading Cx from '" << incxfilename << "'...\n";
		int result = cx. read (incxfilename);
		if (result < 0)
		{
			sout << "ERROR: Can't read from '" << incxfilename <<
				"'.\n";
			return -1;
		}
	}

	// read Cy from an input file if required
	if (incyfilename && *incyfilename)
	{
		sout << "Reading Cy from '" << incyfilename << "'...\n";
		int result = (endomorphism ? cx : cy). read (incyfilename);
		if (result < 0)
		{
			sout << "ERROR: Can't read from '" <<
				incyfilename << "'.\n";
			return -1;
		}
	}

	// read Cx together with the cell map
	sout << "Reading Cx and the map from '" << inmapfilename << "'...\n";
	if (cx. readwithmap (inmapfilename, endomorphism ? cx : cy) < 0)
	{
		sout << "ERROR: Can't read from '" << inmapfilename <<
			"'.\n";
		return -1;
	}

	// complete boundaries in Cx
	sout << "Completing boundaries within Cx...\n";
	int cxsum = cx. makeallboundaries ();
	if (cxsum > 0)
		sout << "* There were " << cxsum << " cells added.\n";

	// prepare two cell complexes for relative homology and read them
	cellcomplex cxrel, cyrel;
	if (relXfilename && *relXfilename)
	{
		sout << "Reading relative Cx from '" << relXfilename <<
			"'...\n";
		int result = cxrel. read (relXfilename);
		if (result < 0)
		{
			sout << "ERROR: Can't read from '" <<
				relXfilename << "'.\n";
			return -1;
		}
		sout << "Completing boundaries within relative Cx...\n";
		int cxrelsum = cxrel. makeallboundaries ();
		if (cxrelsum > 0)
			sout << "* There were " << cxrelsum <<
			" cells added.\n";
	}

	if (!endomorphism && relYfilename && *relYfilename)
	{
		sout << "Reading relative Cy from '" << relYfilename <<
			"'...\n";
		int result = cyrel. read (relYfilename);
		if (result < 0)
		{
			sout << "ERROR: Can't read from '" <<
				relYfilename << "'.\n";
			return -1;
		}
		sout << "Completing boundaries within relative Cy...\n";
		int cyrelsum = cyrel. makeallboundaries ();
		if (cyrelsum > 0)
			sout << "* There were " << cyrelsum <<
				" cells added.\n";
	}

	// make new numbers within Cx (if relative)
	if (relXfilename)
	{
		sout << "Changing numbers in Cx to relative ones...\n";
		cx. makenewnumbers (cxrel);
	}

	// write Cx to an output file as a chain complex
	if (outcxfilename && *outcxfilename)
	{
		sout << "Writing Cx to '" << outcxfilename << "'...\n";
		if (cx. write (outcxfilename) < 0)
		{
			sout << "ERROR: Can't write to '" << outcxfilename <<
				"'.\n";
			return -1;
		}
	}
	else
		sout << "Not writing Cx, because no file name was given.\n";

	if (!endomorphism)
	{
		// complete boundaries in Cy
		sout << "Completing boundaries within Cy where needed...\n";
		int cysum = cy. makeallboundaries ();
		if (cysum > 0)
			sout << "* There were " << cysum <<
				" cells added!\n";

		// make new numbers within Cy (if relative)
		if (relYfilename)
		{
			sout << "Changing numbers in Cy " <<
				"to relative ones...\n";
			cy. makenewnumbers (cyrel);
		}
	}

	if (!endomorphism && outcyfilename && *outcyfilename)
	{
		// write Cy to an output file as a chain complex
		sout << "Writing Cy to '" << outcyfilename << "'...\n";
		if (cy. write (outcyfilename) < 0)
		{
			sout << "ERROR: Can't write to '" <<
				outcyfilename << "'.\n";
			return -1;
		}
	}
	else if (endomorphism)
		sout << "Cy is the same as Cx, " <<
			"as the map is said to be an endomorphism.\n";
	else
		sout << "Not writing Cy, because no file name was given.\n";

	// write the computed chain map to an output file
	sout << "Writing the map to '" << outmapfilename << "'...\n";
	if (cx. writemap (outmapfilename, endomorphism ? &cx : &cy) < 0)
	{
		sout << "ERROR: Can't write to '" << outmapfilename <<
			"'.\n";
		return -1;
	}

	sout << "The conversion of the chain map finished. Thank you.\n";

	return 0;
} /* cnvchmap */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *inmapfilename = NULL;
	char *incxfilename = NULL, *incyfilename = NULL;
	char *outcxfilename = NULL, *outcyfilename = NULL,
		*outmapfilename = NULL;
	char *relXfilename = NULL, *relYfilename = NULL;
	int endomorphism = 0;
	int wrapping_axis = 0;
	coordinate wrap [100];
	for (int i = 0; i < 100; i ++)
		wrap [i] = 0;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, inmapfilename);
	arg (a, NULL, outcxfilename);
	arg (a, NULL, outcyfilename);
	arg (a, NULL, outmapfilename);
	argswitch (a, "e", endomorphism, 1);
	argswitch (a, "a", endomorphism, 1);
	arg (a, "x", incxfilename);
	arg (a, "y", incyfilename);
	arg (a, "r", relXfilename);
	arg (a, "r", relYfilename);
	arg (a, "w", wrap, wrapping_axis, 100);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// set the space wrapping according to the command-line arguments
	for (int i = 0; i < 100; i ++)
		if (wrap [i])
			point::wrap_space (i, wrap [i]);

	// correct file name assignments in case of endomorphism
	if (endomorphism && !outmapfilename)
	{
		outmapfilename = outcyfilename;
		outcyfilename = NULL;
	}

	// check if required file names have been defined
	if (!inmapfilename || !outmapfilename || !outcxfilename)
		argresult = 1;

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
	try
	{
		cnvchmap (inmapfilename, incxfilename, incyfilename,
			outcxfilename, outcyfilename, outmapfilename,
			relXfilename, relYfilename, endomorphism);
		program_time = 1;
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

