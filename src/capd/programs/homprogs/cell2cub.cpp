/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cell2cub.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in May 1999. Last revision: November 22, 2002.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <fstream>
#include <ctime>
#include <cstdlib>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CELLS -> CUBES, ver. 0.02. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: file.cel file.cub [restr.cub].\n\
This is a program which reads a list of cells, i.e. parallelepipeds,\n\
not necessarily (hyper)cubes of size 1, and creates a set of (hyper)cubes\n\
of which all the cells are built. If requested to, it outputs only these\n\
cubes which are in the given set to which the output is to be restricted.\n\
For example, the cell [(0,0) (2,1)] encodes two squares: (0,0) and (1,0).\n\
Parameters:\n\
-w n - wrap the space (repeat for each axis, 0 means no space wrapping),\n\
-h   - show this brief help information only and quit the program.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";

const int maxdim = 100;


// --------------------------------------------------
// ----------------- CELLS -> CUBES -----------------
// --------------------------------------------------

int cells2cubes (const char *inname, const char *outname,
	const char *restrname, const coordinate *wrap)
{
	// read the set of points to which the output is to be restricted
	pointset restricted;
	if (restrname)
	{
		sout << "Reading cubes which restrict the output... ";
		std::ifstream f (restrname);
		if (!f)
			fileerror (restrname);
		f >> restricted;
		sout << restricted. size () << " cubes read.\n";
	}
	
	// show what you are going to do
	sout << "Reading cells from '" << inname << "'... ";

	// open the input file
	std::ifstream in (inname);
	if (!in)
		fileerror (inname);

	// ignore the line with "dimension" from the input file
	ignorecomments (in);
	if (in. peek () == 'd')
	{
		ignoreline (in);
		ignorecomments (in);
	}

	// read the points from the input file
	pointset p;
	int dim = -1;
	int count = 0;
	while (in. peek () == '[')
	{
		// read the opening bracket
		in. get ();
		ignorecomments (in);

		// read the coordinates of the left and right vertex
		coordinate c1 [maxdim], c2 [maxdim];
		int d1 = readcoordinates (in, c1, maxdim);
		ignorecomments (in);
		if (in. peek () == ',')
		{
			in. get ();
			ignorecomments (in);
		}
		int d2 = readcoordinates (in, c2, maxdim);

		// set the dimension of the set of points if necessary
		if (dim < 0)
		{
			dim = d1;
			if ((dim > maxdim) || (dim <= 0) || (d1 != d2))
				throw "Dimension out of range.";
			p. dimension (dim);
			p. wrapspace (wrap);
		}

		// check if the dimension of the read points is valid
		if ((dim != d1) || (dim != d2))
			throw "Wrong space dimension.";

		// add all the points from the rectangle to the set of points
		rectangle r (c1, c2, dim);
		const coordinate *c;
		while ((c = r. get ()) != NULL)
		{
			if (!restrname || restricted. check (c))
				p. add (c);
		}

		// read the closing bracket
		ignorecomments (in);
		in. get ();
		ignorecomments (in);

		count ++;
	}

	// close the input file as it is no more needed
	in. close ();

	sout << count << " cells read.\n";
	sout << "Writing " << p. size () << " points to '" << outname <<
		"'... ";

	// create an output file
	std::ofstream out (outname);
	if (!out)
		fileerror (outname, "create");

	// write the results to this file
	out << p;

	sout << "Done.\n";

	return 0;
} /* cells2cubes */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *inname = NULL, *outname = NULL, *restrname = NULL;
	coordinate wrap [maxdim];
	for (int i = 0; i < maxdim; i ++)
		wrap [i] = 0;
	int wrapping_axis = 0;

	// interprete the command-line parameters
	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	arg (a, NULL, restrname);
	arg (a, "w", wrap, wrapping_axis, maxdim);
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
		return 2;
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
		cells2cubes (inname, outname, restrname,
			wrapping_axis ? wrap : (coordinate *) NULL);
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

