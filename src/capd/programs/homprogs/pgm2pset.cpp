/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file pgm2pset.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 12, 2001. Last revision: February 9, 2003.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/bitcode.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>
#include <cstring>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
PGM -> PointSet, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: infile outfile [[min_color] max_color].\n\
This program creates a set of points from a PGM image.\n\
Parameters:\n\
-p - save the result in the set-of-points format (default),\n\
-b - save the result in the bitcode format,\n\
-c - save the result in the chain-list format,\n\
-u - save the result in the unsorted bitcode format,\n\
-f - fix the minimal corner to 0 (for bitcode); use -fn to fix depth,\n\
-x / -y - fix the X size or the Y size of the input image respectively,\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// ------------------ PGM2POINTSET ------------------
// --------------------------------------------------
#define POINTSET 0
#define BITCODE 1
#define CHAINLIST 2
#define UNSORTEDBITCODE 3

#define MAXWIDTH 8192

pointset *pgm2pointset (char *inname, int lower, int upper,
	int xsize, int ysize)
{
	// open the input file
	std::ifstream in (inname,
		#ifdef ppDOS
		std::ios::binary |
		#endif
		std::ios::in);
	if (!in)
	{
		sout << "Can't open '" << inname << "'.\n";
		return NULL;
	}

	// read the first portion of the binary image (maybe text data)
	char buf [MAXWIDTH];
	int ch = in. get ();
	int pos = 0;
	while ((pos < MAXWIDTH) && (ch != EOF))
	{
		buf [pos ++] = (char) ch;
		ch = in. get ();
	}
	// extract header (if any) or just conclude that this is unreadable
	int i, line = 0;
	int comment = 0;
	for (i = 0; (i < pos) && (line < 2); i ++)
	{
		// if EOL, count it or end a comment
		if (buf [i] == '\n')
		{
			if (comment)
				comment = 0;
			else
				line ++;
		}
		// if a non-important control character, ignore it
		else if ((buf [i] == '\r') || (buf [i] == '\t'));
		// if another control character, then this is binary data
		else if (buf [i] < 32)
		{
			line = 13;
			continue;
		}
		// if a comment begins (or the first line), turn 'comment' ON
		if ((buf [i] == '#') || (buf [i] == 'P'))
			comment = 1;
		// if reading a comment, ignore this character
		if (comment)
			continue;
		// if a number found, read it
		if ((buf [i] >= '0') && (buf [i] <= '9'))
		{
			if (!xsize)
				xsize = std::atoi (buf + i);
			else if (!ysize)
				ysize = std::atoi (buf + i);
			while ((i < pos) &&
				(buf [i] >= '0') && (buf [i] <= '9'))
				i ++;
			i --;
		}
	}

	// if this was binary, rewind to the beginning of the buffer
	if (line >= 13)
		i = 0;

	// if no size defined, assume default 256x256
	if (!xsize && !ysize)
	{
		sout << "Warning: No size defined. Assuming 256x256.\n";
		xsize = ysize = 256;
	}

	// say what picture you are reading
	sout << "Reading a " << xsize << "x" << ysize <<
		" picture from '" << inname << "'...\n";

	// say that the picture is binary
	if (!i)
		sout << "The picture is binary, without header.\n";

	// if the size of the data is incorrect, return NULL
	if ((xsize <= 0) || (ysize <= 0))
	{
		sout << "Wrong size: " << xsize << "x" << ysize << ".\n";
		return NULL;
	}

	pointset *p = new pointset;
	p -> dimension (2);

	// read the data line-by-line
	coordinate point [3];
	int z = 0;
	long pointcounter = 0;
	while (ch != EOF)
	{
		scon << "Reading level " << (z + 1) << '\r';

		point [2] = (coordinate) z;
		for (int y = 0; y < ysize; y ++)
		{
			point [1] = (coordinate) y;
			for (int x = 0; x < xsize; x ++)
			{
				int color;
				if (i < pos)
					color = ((unsigned char *) buf)
						[i ++];
				else
				{
					color = ch;
					ch = in. get ();
				}
				if ((color >= lower) && (color <= upper))
				{
					point [0] = (coordinate) x;
					p -> add (point);
				}
				pointcounter ++;
			}
		}

		// increase the dimension of the set of points if necessary
		if ((ch != EOF) && (p -> dimension () == 2))
		{
			pointset *q = new pointset;
			q -> dimension (3);
			for (int_t j = 0; j < p -> size (); j ++)
			{
				point [0] = (*p) [j] [0];
				point [1] = (*p) [j] [1];
				q -> add (point);
			}
			delete p;
			p = q;
		}

		// take the next level
		z ++;
	}

	// say whether the picture was flat or 3-dimensional
	sout << p -> size () << " points out of " << pointcounter <<
		" in " << z << ((z == 1) ? " level" : " levels") <<
		" read.\n";

	return p;
} /* pgm2pointset */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare the parameters of the program
	char *inname = NULL, *outname = NULL;
	int format = POINTSET;
	int lower = -1, upper = 127;
	int upperread = 0;
	int xsize = 0, ysize = 0;
	int fixed_depth = -1;

	// analyze command-line arguments
	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	arg (a, NULL, lower);
	arg (a, NULL, &upper, upperread, 1);
	argswitch (a, "b", format, BITCODE);
	argswitch (a, "c", format, CHAINLIST);
	argswitch (a, "p", format, POINTSET);
	argswitch (a, "u", format, UNSORTEDBITCODE);
	arg (a, "f", fixed_depth, 0);
	arg (a, "x", xsize);
	arg (a, "y", ysize);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// correct the parameters
	if (lower < 0)
		lower = 0;
	else if (!upperread)
	{
		upper = lower;
		lower = 0;
	}

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if (!outname || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	pointset *p = NULL;

	// try running the main function and catch an error message if thrown
	try
	{
		// read the set of points from the binary file
		p = pgm2pointset (inname, lower, upper, xsize, ysize);
	}
	catch (const char *msg)
	{
		sout << "ERROR: " << msg << '\n';
		return -1;
	}
	catch (...)
	{
		sout << "ABORT: An unknown error occurred.\n";
		return -1;
	}

	if (!p)
		return -1;

	// open a file to write the set of points to
	std::ofstream out (outname);
	if (!out)
	{
		sout << "Cannot write to the file '" << outname <<
			"'.\n";
		return -1;
	}

	// if the set of points is empty, do not write anything
	if (p -> empty ())
	{
		sout << "There are no points to write. " <<
			"Leaving the output set empty.\n";
		delete p;
		return 0;
	}

	// write the set of points to the file
	if ((format == BITCODE) || (format == UNSORTEDBITCODE))
	{
		coordinate *zero = new coordinate [p -> dimension ()];
		for (int i = 0; i < p -> dimension (); i ++)
			zero [i] = 0;
		writebitpoints (out, *p, format == BITCODE,
			fixed_depth, (fixed_depth >= 0) ? zero : NULL);
		delete [] zero;
	}
	else if (format == CHAINLIST)
	{
		sout << "Saving the points to a file...\n";
		int dim = p -> dimension ();
		for (int_t n = 0; n < p -> size (); n ++)
		{
			out << "1 1";
			coordinate *point = (*p) [n];
			for (int i = 0; i < dim; i ++)
				out << " " << point [i];
			for (int i = 0; i < dim; i ++)
				out << " " << (point [i] + 1);
			out << '\n';
		}
	}
	else
	{
		sout << "Saving the points to a file...\n";
		out << "; This is a set of points created from '" <<
			inname << "'.\n" << *p;
	}

	delete p;

	program_time = 1;
	return 0;
} /* main */

/// @}

