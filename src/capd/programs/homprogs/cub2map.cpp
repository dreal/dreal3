/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cub2map.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 11, 2002. Last revision: July 16, 2007.

// Former name(s) of this program: CUB2IDEN.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
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
CUB2MAP, ver. 0.04. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo ="\
Call with: file.cub file.map [-i].\n\
This program has two different functions for creating a map from a full\n\
cubical set. If called without the '-i' switch, it extracts\n\
a combinatorial cubical multivalued map from its graph.\n\
If called with the '-i' switch, it creates a combinatorial cubical\n\
multivalued identity map which maps each full cube to itself.\n\
The latter function may be useful for computing the homomorphism induced\n\
by the inclusion map in homology.\n\
Arguments:\n\
-i - create the cubical identity map,\n\
-c - write the identity map in the 'chmap' format,\n\
-x n - set the dimension of the domain of the map,\n\
-y n - set the dimension of the codomain of the map,\n\
-h - show this brief help information only and quit the program.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";

#ifndef MAXDIM
#define MAXDIM 64
#endif


// --------------------------------------------------
// ------------------- GRAPH2MAP --------------------
// --------------------------------------------------

void splitdim (int dim, int &xdim, int &ydim)
// Split the dimension of the graph to the dimensions of domain and codomain.
// Display warnings or throw error messages if necessary.
{
	// if none of the dimensions is requested
	if (!xdim && !ydim)
	{
		xdim = dim / 2;
		ydim = dim - xdim;
		if (!xdim)
			throw "The dimension of the graph "
				"is too low.";
		if (xdim != ydim)
			sout << "WARNING: The dimension "
				"of the graph is odd.\n";
	}
	// if the dimension of X is to be determined only
	else if (!xdim)
	{
		xdim = dim - ydim;
		if (xdim <= 0)
			throw "The requested dimension of Y "
				"is too high.";
	}
	// if the dimension of Y is to be determined only
	else if (!ydim)
	{
		ydim = dim - xdim;
		if (ydim <= 0)
			throw "The requested dimension of X "
				"is too high.";
	}
	// if both dimensions are already known
	else if (xdim + ydim != dim)
		throw "The dimension of the graph "
			"is different from dim X + dim Y.";
	return;
} /* splitdim */

int graph2map (const char *graphname, const char *mapname,
	int xdim, int ydim)
{
	// open the input file with the graph of the map
	std::ifstream in (graphname);
	if (!in)
		fileerror (graphname);

	// create the output file with the multivalued map
	std::ofstream out (mapname);
	if (!out)
		fileerror (mapname);

	// say what you are doing
	sout << "Reading a graph of a map from '" << graphname << ",\n"
		"and writing the map to '" << mapname << "'...\n";

	// read cells/cubes of the graph and write the map
	coordinate prevleft [MAXDIM], prevright [MAXDIM];
	int count = 0;
	int dimension = 0;
	bool thefirst = true;
	while (1)
	{
		// read the next point or cell in the domain of the map
		coordinate left [MAXDIM], right [MAXDIM];
		int domtype;
		int dim = readcubeorcell (in, left, right, MAXDIM, &domtype);
		if (dim <= 0)
			break;

		// update the counter
		count ++;

		// if this is the first element, make initial adjustments
		if (!dimension)
		{
			// split the dimension
			splitdim (dim, xdim, ydim);

			// keep the dimension for future reference
			dimension = dim;
		}
		// otherwise check the dimension
		else if (dim != dimension)
		{
			sout << count << ' ';
			throw "Inconsistent dimension of graph elements.";
		}

		// check if the domain element should be written
		bool newelement = thefirst;
		for (int i = 0; (i < xdim) && !newelement; i ++)
			if ((left [i] != prevleft [i]) ||
				(right [i] != prevright [i]))
				newelement = true;

		// remember this element if necessary
		for (int i = 0; (i < xdim) && newelement; i ++)
		{
			prevleft [i] = left [i];
			prevright [i] = right [i];
		}

		// close the previous image if necessary
		if (newelement && !thefirst)
			out << "}\n";

		// write the domain element of the map if necessary
		if (newelement)
		{
			if (domtype == CUBE)
				write (out, left, xdim);
			else if (domtype == CELL)
			{
				out << '[';
				write (out, left, xdim);
				out << ' ';
				write (out, right, xdim);
				out << ']';
			}
			out << " -> {";
		}

		// write the image element of the map
		if (!newelement)
			out << ' ';
		if (domtype == CUBE)
			write (out, left + xdim, ydim);
		else if (domtype == CELL)
		{
			out << '[';
			write (out, left + xdim, ydim);
			out << ' ';
			write (out, right + xdim, ydim);
			out << ']';
		}

		// this is no longer the first element
		thefirst = false;

		if (!(count % 4373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
	}

	// close the last image in the map
	if (!thefirst)
		out << "}\n";

	// indicate the summary and finish
	sout << count << " elements of the graph processed.\n";

	return 0;
} /* graph2map */


// --------------------------------------------------
// -------------------- CUB2IDEN --------------------
// --------------------------------------------------

int cubes2identity (char *inname, char *outname, bool chmapformat)
{
	// show what you are going to do
	sout << "Transforming cubes to the identity map... ";

	// open the input file
	std::ifstream in (inname);
	if (!in)
		fileerror (inname);

	// create the output file
	std::ofstream out (outname);
	if (!out)
		fileerror (outname, "create");

	// read the points and write them to the output file
	int dim = 0;
	int count = 0;
	while (1)
	{
		// skip comments and check if this is not the end of the file
		ignorecomments (in);
		if (in. eof ())
			break;
		if (in. peek () == 'd')
		{
			ignoreline (in);
			continue;
		}

		// read the next point or cell in the set
		coordinate left [MAXDIM], right [MAXDIM];
		int celltype;
		int d = readcubeorcell (in, left, right, MAXDIM, &celltype);
		if (d <= 0)
			break;

		// set the dimension of the set of points if necessary
		if (dim <= 0)
			dim = d;

		// check if the dimension of the read point is valid
		else if (dim != d)
			throw "Wrong space dimension.";

		// write the map header if necessary
		if (!count && chmapformat)
			out << "Space Dimension: " << dim << "\n\n"
				"Number Of Primitive Arguments: 00000000\n\n"
				"Map: AlmostPerfect\n\n\n"
				" Primitive Argument             "
				"Value\n\n";

		// write the entry corresponding to this cube
		if (chmapformat || (celltype == CELL))
		{
			out << '[';
			write (out, left, dim);
			out << ' ';
			write (out, right, dim);
			if (chmapformat)
				out << "] [";
			else
				out << "] -> {[";
			write (out, left, dim);
			out << ' ';
			write (out, right, dim);
			if (chmapformat)
				out << "]\n";
			else
				out << "]}\n";
		}
		else
		{
			write (out, left, dim);
			out << " -> {";
			write (out, left, dim);
			out << "}\n";
		}

		if (!(count % 4373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";

		count ++;
	}
	if (chmapformat)
		out << "\nEND\n";

	sout << count << " elements processed.\n";
	return 0;
} /* cubes2identity */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *inname = NULL, *outname = NULL;
	int xdim = 0, ydim = 0;
	bool chmapformat = false;
	bool iden = false;

	// interprete the command-line parameters
	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	arg (a, "x", xdim);
	arg (a, "y", ydim);
	argswitch (a, "c", chmapformat, true);
	argswitch (a, "i", iden, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// verify the dimensions
	if ((xdim < 0) || (ydim < 0))
	{
		sout << "Incorrect dimensions selected: -x " << xdim <<
			" -y " << ydim << ".\n";
		argresult = -1;
	}

	// if there not enough file names, only display help
	if (!inname || !outname)
		argresult = 1;

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return -1;
	}

	// show help information if requested to
	if (argresult > 0)
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		if (iden)
			cubes2identity (inname, outname, chmapformat);
		else
			graph2map (inname, outname, xdim, ydim);
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

