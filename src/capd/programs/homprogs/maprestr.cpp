/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file maprestr.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on September 17, 2002. Last revision: November 23, 2002.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <cstdlib>
#include <ctime>
#include <new>
#include <iostream>
#include <fstream>
#include <iomanip>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
MAPRESTR, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: input.map domain.cub output.map.\n\
This program reads a multivalued cubical map from the input text file\n\
and writes this map restricted to the new domain to an output file.\n\
For input, each line should have the following form:\n\
either \"(-1,-42) -> {(1,12) (2,12) (2,13) (3,13)}\",\n\
or \"[(-1,-42,295) (0,-41,296)] [(-15,-46,149) (-13,-43,154)]\".\n\
Switches and additional arguments:\n\
-h   - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";

#ifndef MAXDIM
#define MAXDIM 64
#endif


// --------------------------------------------------
// -------------------- MAPRESTR --------------------
// --------------------------------------------------

int maprestr (char *inname, char *domname, char *outname)
{
	// read the new domain from a file
	pointset domain;
	{
		sout << "Reading the map domain from '" << domname <<
			"'... ";
		std::ifstream dom (domname);
		if (!dom)
			fileerror (domname);
		dom >> domain;
		sout << domain. size () << " cubes read.\n";
	}

	// open the input map file
	std::ifstream inmap (inname);
	if (!inmap)
		fileerror (inname);

	// open the output map file
	std::ofstream outmap (outname);
	if (!outmap)
		fileerror (outname, "create");

	// say what you are doing
	sout << "Reading a multivalued cubical map from '" << inname <<
		"'\n" << "and writing its restriction to '" << outname <<
		"'...\n";

	// prepare a counter
	int incounter = 0, outcounter = 0;

	// read the map and process it
	bool chmapformat = false;
	ignorecomments (inmap);
	while (1)
	{
		// go to the next point or cell in the map
		while ((inmap. peek () != '[') && (inmap. peek () != '(') &&
			(inmap. peek () != '{') && (inmap. peek () != '<'))
		{
			ignoreline (inmap);
			ignorecomments (inmap);
			if (!inmap)
				break;
		}
		if (!inmap)
			break;

		// try reading a point
		coordinate point [MAXDIM];
		int dim = readcoordinates (inmap, point, MAXDIM);
		ignorecomments (inmap);

		// if successful, this is the map in my format
		bool myformat = (dim > 0);

		// read the point if not successful previously
		if (dim <= 0)
		{
			// if an error is set for the map, clear it
			inmap. clear (inmap. rdstate () & ~std::ios::failbit);

			// read the first point for the argument cell
			dim = readcoordinates (inmap, point, MAXDIM);
			ignorecomments (inmap);
		}

		// if cannot read a point, then this is wrong
		if (dim <= 0)
			throw "Cannot read a domain cube.";

		// check if this point is in the domain of the restriction
		bool good = domain. check (point);
		if (good)
			domain. remove (point);

		if (!good)
		{
			ignoreline (inmap);
			ignorecomments (inmap);
		}
		else if (myformat)
		{
			// write the argument point to the output map
			write (outmap, point, dim);

			// read the arrow
			if ((inmap. get () != '-') || (inmap. get () != '>'))
				throw "An arrow in the map expected.";
			ignorecomments (inmap);

			// read the opening parenthesis of the list of cubes
			int closing = readparenthesis (inmap);
			if (closing == EOF)
				throw "Unexpected end of file.";
			ignorecomments (inmap);

			// copy the list of image cubes
			outmap << " -> {";
			bool firstpoint = true;
			while (inmap. peek () != closing)
			{
				// read the cube
				int d = readcoordinates (inmap, point,
					MAXDIM);
				ignorecomments (inmap);

				// check its dimension
				if (d <= 0)
					throw "Can't read an image point.";

				// add a space unless this is the first point
				if (firstpoint)
					firstpoint = false;
				else
					outmap << ' ';

				// add this cube to suitable sets
				write (outmap, point, dim);

				// ignore a comma if there is one
				if (inmap. peek () == ',')
				{
					inmap. get ();
					ignorecomments (inmap);
				}
			}

			// read the closing parenthesis from the input map
			inmap. get ();
			ignorecomments (inmap);

			// write the closing parenthesis to the output map
			outmap << "}\n";
		}
		// otherwise, this line is in the "chmap" format
		else
		{
			if (!outcounter)
			{
				outmap << "Space Dimension: " <<
					domain. dimension () << "\n\n"
					"Number Of Primitive Arguments: " <<
					(domain. size () + 1) << "\n\n"
					"Map: AlmostPerfect\n\n\n"
					" Primitive Argument             "
					"Value\n\n";
				chmapformat = true;
			}

			// write the first argument corner to the output map
			outmap << '[';
			write (outmap, point, dim);

			// copy the other corner of the argument cube
			readcoordinates (inmap, point, MAXDIM);
			ignorecomments (inmap);
			outmap << ' ';
			write (outmap, point, dim);

			// read and write two brackets
			inmap. get ();
			ignorecomments (inmap);
			inmap. get ();
			ignorecomments (inmap);
			outmap << "] [";

			// copy two points for the image cell
			readcoordinates (inmap, point, MAXDIM);
			ignorecomments (inmap);
			write (outmap, point, dim);
			outmap << ' ';
			readcoordinates (inmap, point, MAXDIM);
			write (outmap, point, dim);

			// read the closing bracket and write one
			inmap. get ();
			ignorecomments (inmap);
			outmap << "]\n";
		}

		// update the output map counter
		if (good)
			outcounter ++;

		// update the input map counter and display it if necessary
		incounter ++;
		if (!(incounter % 373))
			scon << std::setw (10) << incounter <<
				"\b\b\b\b\b\b\b\b\b\b";
	}
	if (chmapformat)
		outmap << "\nEND\n";

	sout << incounter << " units read, " << outcounter << " written.\n";
	if (!domain. empty ())
		sout << "Warning: The map was not defined on some cubes "
			"from the domain.\n";

	return 0;
} /* map2pset */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed.
{
	// prepare user-configurable variables
	char *inname = NULL, *outname = NULL, *domname = NULL;

	// interprete the command-line arguments
	arguments a;

	arg (a, NULL, inname);
	arg (a, NULL, domname);
	arg (a, NULL, outname);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// if there were errors, inform about it end exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return -1;
	}

	// display help info if necessary
	if (argresult || !outname)
	{
		sout << helpinfo << '\n';
		return 1;
	}

	int result;
	try
	{
		result = maprestr (inname, domname, outname);
		program_time = 1;
		return result;
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

