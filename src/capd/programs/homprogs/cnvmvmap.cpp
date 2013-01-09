/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cnvmvmap.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Written on March 5, 2002. Last revision: September 9, 2004.


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

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CNVMVMAP, ver. 0.02. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: infile.map outfile.map [-c].\n\
This program converts a multivalued cubical map from the format used in\n\
'chmap' by Marcin Mazur and Jacek Szybowski to a more general format\n\
in which each cube is mapped to a set of cubes, not necessarily convex.\n\
Called with '-c', it converts the map backwards (to certain extent).\n\
This program is capable of reading a mixed map, in which some lines are\n\
in the '[cell] [cell]' format, and others in the 'x -> {set}' format.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// -------------------- CNVMVMAP --------------------
// --------------------------------------------------

const int maxdim = 32;

class onepoint
{
public:
	onepoint (const coordinate *coord, int dim):
		c (coord), d (dim) {}
	friend std::ostream &operator << (std::ostream &out, const onepoint &p)
	{
		for (int i = 0; i < p. d; i ++)
			out << (i ? ',' : '(') << p. c [i];
		out << ')';
		return out;
	} /* operator << */

protected:
	const coordinate *c;
	int d;
}; /* onepoint */

void copyline (std::istream &in, int ch, std::ostream &out)
// Copy the entire line and put the given character at the beginning.
{
	while ((ch != EOF) && (ch != '\n'))
	{
		out. put ((char) ch);
		ch = in. get ();
	}
	if (ch == '\n')
		out. put ((char) ch);
	ignorecomments (in);
	return;
} /* copyline */

int cnvmvmap (const char *inname, const char *outname, bool convex)
{
	// open the input file
	std::ifstream in (inname);
	if (!in)
	{
		sout << "Can't open the input file.\n";
		return -1;
	}

	// open the output file
	std::ofstream out (outname);
	if (!out)
	{
		sout << "Can't create the output file.\n";
		return -1;
	}

	// write the header of the map with convex images if asked to
	if (convex)
	{
		out << "Space Dimension: 0\n\n";
		out << "Number Of Primitive Arguments: 0\n\n";
		out << "Map: AlmostPerfect\n\n\n";
		out << " Primitive Argument             Value\n\n";
	}
	
	// prepare assignment counters
	long copycounter = 0, transcounter = 0, igncounter = 0;

	// transform all the lines of the map
	ignorecomments (in);
	while (in. peek () != EOF)
	{
		// ignore the entire line if it does not begin with a bracket
		if (closingparenthesis (in. peek ()) == EOF)
		{
			ignoreline (in);
			ignorecomments (in);
			++ igncounter;
			continue;
		}

		// read the opening bracket
		int ch = in. get ();
		ignorecomments (in);

		// if the line is in the right format, just copy it
		int nextclosing = closingparenthesis (in. peek ());
		if ((convex && (nextclosing != EOF)) ||
			(!convex && (nextclosing == EOF)))
		{
			// copy the entire line to the output file
			copyline (in, ch, out);

			// increase the copy assignment counter
			++ copycounter;
			continue;
		}

		// read the argument cube or cell
		coordinate argleft [maxdim];
		int dim = readcoordinates (in, argleft, maxdim,
			convex ? closingparenthesis (ch) : EOF);
		ignorecomments (in);

		// read the right vertex of the argument cell if necessary
		if (closingparenthesis (in. peek ()) != EOF)
		{
			coordinate argright [maxdim];
			readcoordinates (in, argright, maxdim);
			ignorecomments (in);
		}

		if (convex)
		{
			// write the argument cell
			out << '[' << onepoint (argleft, dim);
			for (int i = 0; i < dim; ++ i)
				argleft [i] ++;
			out << onepoint (argleft, dim) << "] [";

			// prepare the minimal and maximal coordinate sets
			coordinate minimal [maxdim], maximal [maxdim];
			
			// count the cubes read
			int counter = 0;
			
			// read the arrow
			while (in. peek () == '-')
				in. get ();
			if (in. peek () == '>')
				in. get ();
			ignorecomments (in);

			// read the opening brace
			in. get ();
			ignorecomments (in);
			
			// read all the cubes
			bool firsttime = true;
			while (closingparenthesis (in. peek ()) != EOF)
			{
				// read the cube
				coordinate cur [maxdim];
				readcoordinates (in, cur, maxdim);
				ignorecomments (in);
				++ counter;

				// update the min/max coordinates
				for (int i = 0; i < dim; ++ i)
				{
					if (firsttime ||
						(minimal [i] > cur [i]))
						minimal [i] = cur [i];
					if (firsttime ||
						(maximal [i] - 1 < cur [i]))
						maximal [i] = (coordinate)
							(cur [i] + 1);
				}
				firsttime = false;
			}

			// read the closing brace
			in. get ();
			ignorecomments (in);

			// if there were no cubes, this is an error
			if (!counter)
			{
				sout << "The image of " << onepoint (argleft,
					dim) << " is empty. Cancelling.\n";
				return -1;
			}

			// write the image of the cube
			out << onepoint (minimal, dim) <<
				onepoint (maximal, dim) << "]\n";
		}
		else
		{
			// read the closing and opening brackets
			in. get ();
			ignorecomments (in);
			in. get ();
			ignorecomments (in);

			// read the value cell
			coordinate vleft [maxdim], vright [maxdim];
			readcoordinates (in, vleft, maxdim);
			ignorecomments (in);
			readcoordinates (in, vright, maxdim);
			ignorecomments (in);

			// if there was an error, break the process
			if (!in || !out || (in. peek () == EOF))
			{
				sout << "An error occurred. Interrupting.\n";
					if (copycounter + transcounter)
					sout << "(Only " << (copycounter +
						transcounter) <<
						" assignments analyzed.)\n";
				return -1;
			}

			// read the closing bracket
			in. get ();
			ignorecomments (in);

			// make a rectangle from the value cell
			rectangle r (vleft, vright, dim);

			// write the assignment to the output file
			out << onepoint (argleft, dim) << " -> {";
			const coordinate *p = r. get ();
			while (p)
			{
				out << onepoint (p, dim);
				p = r. get ();
				if (p)
					out << ' ';
				else
					out << "}\n";
			}
		}
		// increase the transformed assignment counter
		++ transcounter;
	}

	sout << transcounter << " assignments translated, " << copycounter <<
		" copied, " << igncounter << " lines ignored.\n";
	return 0;
} /* cnvmvmap */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *inname = NULL, *outname = NULL;
	bool convex = false;

	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	argswitch (a, "c", convex, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// check if required file names have been defined
	if (!inname || !outname)
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
		cnvmvmap (inname, outname, convex);
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

