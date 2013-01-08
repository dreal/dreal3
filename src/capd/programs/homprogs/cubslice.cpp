/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubslice.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Written on May 15, 2002. Last revision: November 14, 2006.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/cubisets.h"
#include "capd/homology/cubmaps.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <cstdlib>
#include <sstream>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CUBSLICE, ver. 0.02. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: infile.cub/map outfile (without extension).\n\
This program reads a set of cubes or a multivalued cubical map stored in\n\
the input file and then writes slices to output files. The number of each\n\
slice (starting with 1) and a file extension ('cub' or 'map') is appended\n\
to the given output file name.\n\
Switches and additional arguments:\n\
-p n - set the number of pieces; default is 8,\n\
-m n - set the maximal number of cubes in each part (overrides -p),\n\
-a n - select the axis (from 1 to DIM), default is 0 (find optimal),\n\
-o n - overlap pieces (-o <=> -o 1), default is 0 unless -s used,\n\
-s filename - save the overlapping pieces to files,\n\
-h   - show this brief help information only.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// -------------------- CUBSLICE --------------------
// --------------------------------------------------

enum filetypes {setofcubes, multivaluedcubicalmap, almostperfectmap};

int readcubes (const char *filename, cubes &X)
// Read cubes and return the type of the file: setofcubes or cubicalmap.
{
	// open the input file
	std::ifstream in (filename);
	if (!in)
		fileerror (filename);

	// check the first character in the file
	ignorecomments (in);
	int ch = in. peek ();
	if (ch == 'd')
	{
		ignoreline (in);
		ignorecomments (in);
		ch = in. peek ();
	}

	// if this is not an opening parenthesis, this is an almost perf. map
	if (closingparenthesis (ch) == EOF)
	{
		sout << "Reading the domain of an almost perfect map... ";
		readdomain (in, X);
		sout << X. size () << " cubes read.\n";
		return almostperfectmap;
	}

	// read the first cube and check the next available character
	cube q;
	in >> q;
	ignorecomments (in);

	// if this is the beginning of "->", then this is a multiv. cub. map
	if (in. peek () == '-')
	{
		sout << "Reading the domain of a multivalued map from '" <<
			filename << "'... ";
		in. seekg (0);
		readdomain (in, X);
		sout << X. size () << " cubes read.\n";
		return multivaluedcubicalmap;
	}

	// otherwise this is a set of cubes
	sout << "Reading cubes from '" << filename << "'... ";
	X. add (q);
	in >> X;
	sout << X. size () << " cubes read.\n";
	return setofcubes;
} /* readcubes */

int writepiece (const char *inname, const std::string &outname, const cubes &X,
	int filetype)
// Write the given piece of a set of cubes to a file.
// If 'filetype' is different from 'setofcubes', copy a suitable portion
// of the multivalued cubical map stored in the input file to the output one.
{
	std::ofstream out (outname. c_str ());
	if (!out)
		fileerror ("create");
	if (filetype == setofcubes)
		out << X;
	else
	{
		std::ifstream in (inname);
		if (!in)
			fileerror ("open");
		cubicalmap m;
		readselective (in, X, m);
		out << m;
	}
	return 0;
} /* writepiece */

const char *zeronumber (int width, int number)
// Prepare a string containing the given number written with preceding zeros.
{
	static char s [16];
	if (width >= 16)
		throw "Number too large.";
	for (int i = 0; i < width; i ++)
		s [i] = '0';
	s [width] = 0;
	for (int cur = width - 1; cur >= 0; cur --)
	{
		s [cur] = (char) ('0' + (number % 10));
		number /= 10;
	}
	return s;
} /* zeronumber */

int writepieces_single (const char *inname, const char *outname,
	const multitable<cubes> &Y, int n, int filetype)
// Write the given pieces to the files whose names are based on 'outname'.
{
	// calculate the widths of numbers
	int width = 1;
	int m = n;
	while (m >= 10)
	{
		width ++;
		m /= 10;
	}

	// write all the pieces to files
	for (int piece = 0; piece < n; piece ++)
	{
		std::ostringstream s;
		s << outname << zeronumber (width, piece + 1) <<
			((filetype == setofcubes) ? ".cub" : ".map");
		const std::string filename = s. str ();
		sout << "Writing '" << filename << "'... ";
		writepiece (inname, filename, Y (piece), filetype);
		sout << Y (piece). size () << " elements written.\n";
	}

	return 0;
} /* writepieces_single */

int writepieces (const char *inname, const char *outname,
	const multitable<cubes> &Y, int n, int filetype)
// Write the given pieces to the files whose names are based on 'outname'.
{
	// if the file type is just a set of cubes, write single pieces
	if (filetype == setofcubes)
		return writepieces_single (inname, outname, Y, n, filetype);

	// calculate the widths of numbers
	int width = 1;
	int m = n;
	while (m >= 10)
	{
		width ++;
		m /= 10;
	}

	// open the input file for reading
	std::ifstream in (inname);
	if (!in)
		fileerror (inname);

	// open all the output files simultaneously
	std::ofstream *out = new std::ofstream [n];
	if (!out)
		throw "Can't create a table of output streams.";
	sout << "Writing " << n << " pieces simultaneously "
		"to the following files:\n";
	for (int piece = 0; piece < n; piece ++)
	{
		// open a suitable file
		std::ostringstream s;
		s << outname << zeronumber (width, piece + 1) <<
			((filetype == setofcubes) ? ".cub" : ".map");
		const std::string filename = s. str ();
		out [piece]. open (filename. c_str ());
		if (!out [piece])
			fileerror (filename. c_str (), "create");
		sout << (piece ? ", " : "") << filename << " (" <<
			Y (piece). size () << ')';

		// write the beginning of the file
		out [piece] << "; This is part " << (piece + 1) <<
			" out of " << n << " of '" << inname << "' (" <<
			Y (piece). size () << " elements).\n\n";
		switch (filetype)
		{
			case almostperfectmap:
				out [piece] << "Space Dimension: " <<
					Y (piece) [1]. dim () << "\n\n"
					"Number Of Primitive Arguments: " <<
					Y (piece). size () << "\n\n"
					"Map: AlmostPerfect\n\n"
					"Primitive Argument    Value\n\n";
				break;
			default:
				break;
		}
	}
	sout << '\n';

	ignorecomments (in);
	while (!in. eof () && closingparenthesis (in. peek ()) == EOF)
	{
		ignoreline (in);
		ignorecomments (in);
	}

	// distribute the input file among the output files
	while (closingparenthesis (in. peek ()) != EOF)
	{
		// ignore the first bracket if necessary
		if (filetype == almostperfectmap)
		{
			in. get ();
			ignorecomments (in);
		}

		// read the domain cube
		cube q;
		in >> q;
		ignorecomments (in);

		// determine the set
		int number1 = 0;
		while (!Y (number1). check (q))
		{
			number1 ++;
			if (number1 >= n)
				throw "Cube not found.";
		}
		int number2 = -1;
		if ((number1 < n - 1) && (Y (number1 + 1). check (q)))
			number2 = number1 + 1;

		// write the element to a suitable file
		if (filetype == almostperfectmap)
		{
			// read the other cube
			cube r;
			in >> r;
			ignorecomments (in);
			// ignore ']' and '['
			in. get ();
			ignorecomments (in);
			in. get ();
			ignorecomments (in);
			// read the image vertices
			cube left, right;
			in >> left;
			ignorecomments (in);
			in >> right;
			ignorecomments (in);
			// ignore ']'
			in. get ();
			ignorecomments (in);

			// write the element to the output files
			out [number1] << '[' << q << ' ' << r <<
				"] [" << left << ' ' << right << "]\n";
			if (number2 >= 0)
				out [number1] << '[' << q << ' ' << r <<
					"] [" << left << ' ' << right <<
					"]\n";
		}
		else
		{
			// ignore "->"
			if (in. get () != '-')
				throw "'->' expected but not found.";
			ignorecomments (in);
			if (in. get () != '>')
				throw "Should be '->'.";
			ignorecomments (in);

			// write the domain element to both files
			out [number1] << q << " -> {";
			if (number2 >= 0)
				out [number2] << q << " -> {";

			// copy the image to both files
			int closing = closingparenthesis (in. get ());
			ignorecomments (in);
			bool continuing = false;
			while (in. peek () != closing)
			{
				in >> q;
				ignorecomments (in);
				if (in. peek () == ',')
				{
					in. get ();
					ignorecomments (in);
				}
				if (continuing)
					out [number1] << ' ';
				out [number1] << q;
				if (number2 >= 0)
				{
					if (continuing)
						out [number2] << ' ';
					out [number2] << q;
				}
				continuing = true;
			}

			// ignore the closing parenthesis
			in. get ();
			ignorecomments (in);

			// copy the end of the image to both files
			out [number1] << "}\n";
			if (number2 >= 0)
				out [number2] << "}\n";
		}
	}

	// write the end of the file in the suitable format
	for (int piece = 0; piece < n; piece ++)
		out [piece] << ((filetype == almostperfectmap) ?
			"end\n" : "; the end\n");
	delete [] out;

	return 0;
} /* writepieces */

int sliceit (cubes &X, multitable<cubes> &Y, multitable<cubes> *O,
	int parts, int axis, int overlap, int maxcubes)
// Divide the set of cubes X into pieces following the specification given.
// Return the actual number of pieces stored in Y.
{
	// prepare the number of pieces
	int n = 1;

	// extract the range of coordinates of all the cubes in X
	sout << "Analyzing the cubes... ";
	coordinate mincoord [cube::MaxDim];
	coordinate maxcoord [cube::MaxDim];
	coordinate coord [cube::MaxDim];
	int dim = 0;
	for (int_t i = 0; i < X. size (); ++ i)
	{
		const cube &q = X [i];
		if (!dim)
			dim = q. dim ();
		else if (dim != q. dim ())
			throw "Not all the cubes are of the same dimension.";
		q. coord (coord);
		for (int j = 0; j < dim; j ++)
		{
			if (!i || (mincoord [j] > coord [j]))
				mincoord [j] = coord [j];
			if (!i || (maxcoord [j] < coord [j]))
				maxcoord [j] = coord [j];
		}
	}
	sout << "Done.\n";

	// if no coordinate axis is given, choose something
	if (!axis)
	{
		for (int j = 1; j < dim; j ++)
			if ((maxcoord [axis] - mincoord [axis]) <
				(maxcoord [j] - mincoord [j]))
				axis = j;
	}
	// otherwise decrease the axis number to be between 0 and dim-1
	else
		axis --;
	sout << "Using the axis no. " << (axis + 1) << ". ";
	if (overlap == 1)
		sout << "Overlapping one layer.\n";
	else if (overlap)
		sout << "Overlapping " << overlap << " layers.\n";
	else
		sout << "No overlapping.\n";

	// count the number of cubes in each layer
	int ncount = maxcoord [axis] - mincoord [axis] + 1;
	sout << "Slicing through " << ncount <<
		" layers in the range from " << mincoord [axis] <<
		" to " << maxcoord [axis] << ":\n";
	int_t *count = new int_t [ncount];
	int_t *part1 = new int_t [ncount];
	int_t *part2 = new int_t [ncount];
	if (!count || !part1 || !part2)
		sout << "Can't prepare a table for counting layers.";
	for (int i = 0; i < ncount; i ++)
		count [i] = 0;
	for (int_t i = 0; i < X. size (); i ++)
	{
		X [i]. coord (coord);
		count [coord [axis] - mincoord [axis]] ++;
	}

	// adjust the number of parts
	if (!parts && !maxcubes)
		parts = 8;

	// prepare the maximal number of cubes in each part if not given
	if (!maxcubes && parts)
	{
		maxcubes = (X. size () + parts - 1) / parts;
		if (overlap)
			maxcubes += X. size () / 2 * overlap / ncount;
	}

	int already = 0;
	sout << '[' << mincoord [axis] << ',';
	for (int i = 0; i < ncount; i ++)
	{
		already += count [i];
		if ((already > maxcubes) && (!parts || (n < parts)))
		{
			sout << (mincoord [axis] + i - 1) << ']';
			n ++;
			int prev = i - overlap;
			if (prev < 0)
				prev = 0;
			already = 0;
			sout << ", [" << (mincoord [axis] + prev) << ',';
			while (prev < i)
			{
				part2 [prev] = n - 1;
				already += count [prev];
				prev ++;
			}
		}
		part1 [i] = part2 [i] = n - 1;
	}
	delete [] count;
	sout << maxcoord [axis] << "]\n";

	// move cubes from X to the other parts
	sout << "Slicing the set of cubes into pieces... ";
	while (!X. empty ())
	{
		int_t k = X. size () - 1;
		X [k]. coord (coord);
		int index = coord [axis] - mincoord [axis];
		Y [part1 [index]]. add (X [k]);
		if (part1 [index] != part2 [index])
		{
			Y [part2 [index]]. add (X [k]);
			if (O)
			{
				(*O) [part1 [index]]. add (X [k]);
				(*O) [part2 [index]]. add (X [k]);
			}
		}
		X. removenum (k);
	}
	sout << n << " parts created.\n";

	delete [] part1;
	delete [] part2;

	return n;
} /* sliceit */

int cubslice (const char *inname, const char *outname,
	const char *overlapname,
	int parts, int axis, int overlap, int maxcubes)
{
	// read the cubes
	cubes X;
	int filetype = readcubes (inname, X);

	// if no cubes have been read, we are done
	if (X. empty ())
	{
		sout << "No cubes read. No output files written.\n";
		return 0;
	}

	// divide the set of cubes into pieces
	multitable<cubes> Y, O;
	int n = sliceit (X, Y, overlapname ? &O : NULL,
		parts, axis, overlap, maxcubes);

	// write the pieces
	writepieces (inname, outname, Y, n, filetype);
	if (overlapname)
		writepieces (inname, overlapname, O, n, filetype);

	return 0;
} /* cubslice */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *inname = NULL, *outname = NULL, *overlapname = NULL;
	int parts = 0, axis = 0, overlap = 0, maxcubes = 0;

	// analyze the command line
	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	arg (a, "s", overlapname);
	arg (a, "p", parts);
	arg (a, "a", axis);
	arg (a, "o", overlap, 1);
	arg (a, "m", maxcubes);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's title
	if (argresult >= 0)
		sout << title << '\n';

	// adjust the arguments
	if (overlapname && !overlap)
		overlap = 1;

	// if there are not enough file names, help should be displayed
	if (!inname || !outname)
		argresult = 1;

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with -h for help.\n";
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
		cubslice (inname, outname, overlapname,
			parts, axis, overlap, maxcubes);
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

