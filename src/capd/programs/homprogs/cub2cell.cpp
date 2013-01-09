/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cub2cell.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on September 28, 1999. Last revision: November 23, 2002.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <iomanip>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CUBES -> CELLS, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo ="\
Call with: file.cub file.cel.\n\
This is a program which reads a list of cubes of size 1 represented by\n\
their corner with minimal coordinates, and writes this set of cubes to the\n\
output file in the form of cells represented by two opposite corners.\n\
Note: The program copies the input to the output, only changing format.\n\
For example, the cube (0,0) will be transformed to the cell [(0,0) (1,1)].\n\
Parameters:\n\
-w n - wrap the space (repeat for each axis, 0 means no space wrapping),\n\
-c   - use the 'chl' format compatible with 'chlv' by Marc Niethammer's,\n\
-h   - show this brief help information only and quit the program.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";

#ifndef MAXDIM
#define MAXDIM 64
#endif


// --------------------------------------------------
// -------------------- CUBCELLS --------------------
// --------------------------------------------------

int cubes2cells (char *inname, char *outname, const coordinate *wrap,
	bool chl)
{
	// show what you are going to do
	sout << "Transforming cubes to cells... ";

	// open the input file
	std::ifstream in (inname);
	if (!in)
		fileerror (inname);

	// create the output file
	std::ofstream out (outname);
	if (!out)
		fileerror (outname, "create");

	// write the header to the output file
	if (!chl)
		out << "; These are cells created from '" << inname <<
			"'.\n";

	// read the points and write them to the output file
	// ignore the line with "dimension" from the input file
	ignorecomments (in);
	if (in. peek () == 'd')
	{
		ignoreline (in);
		ignorecomments (in);
	}

	int dim = -1;
	int count = 0;
	while ((in. peek () == '[') || (in. peek () == '(') ||
		(in. peek () == '{') || (in. peek () == '<'))
	{
		coordinate c [MAXDIM];
		int d = readcoordinates (in, c, MAXDIM);
		ignorecomments (in);

		// set the dimension of the set of points if necessary
		if (dim < 0)
			dim = d;

		// check if the dimension of the read point is valid
		if (dim != d)
			throw "Wrong space dimension.";

		// wrap the point if necessary
		if (wrap)
			wrapcoord (c, c, wrap, dim);

		// write the cell corresponding to this cube
		if (chl)
		{
			out << "1 1";
			for (int i = 0; i < dim; i ++)
				out << ' ' << c [i];
			for (int i = 0; i < dim; i ++)
				out << ' ' << (c [i] + 1);
			out << '\n';
		}
		else
		{
			out << '[';
			write (out, c, dim);
			out << ' ';
			for (int i = 0; i < dim; i ++)
				c [i] ++;
			write (out, c, dim);
			out << "]\n";
		}

		if (!(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";

		count ++;
	}

	sout << count << " cubes processed.\n";
	return 0;
} /* cubes2cells */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *inname = NULL, *outname = NULL;
	coordinate wrap [MAXDIM];
	for (int i = 0; i < MAXDIM; i ++)
		wrap [i] = 0;
	int wrapping_axis = 0;
	bool chl = false;

	// interprete the command-line parameters
	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	arg (a, "w", wrap, wrapping_axis, MAXDIM);
	argswitch (a, "c", chl, true);
	arghelp (a);

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
		return -1;
	}

	// if help requested or no filenames present, show help information
	if (!inname || !outname || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		cubes2cells (inname, outname, wrap, chl);
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

