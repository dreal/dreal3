/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bit2pset.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 12, 2001. Last revision: November 23, 2002.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/bitcode.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
BitCode2PointSet, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: infile outfile.\n\
This program converts a set of points from the bitcode format\n\
to the list-of-cubes format. The direction of conversion\n\
is determined automatically depending on the contents of the file.\n\
Parameters:\n\
-u   - save unsorted bitcodes (if converting to the bitcode format),\n\
-f   - fix the minimal corner to 0 (for writing bitcodes only),\n\
-f n - set the depth of bit codes (for writing bitcodes only),\n\
-h   - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// --------------- BITCODE 2 POINTSET ---------------
// --------------------------------------------------

int bitcode2pointset (char *inname, char *outname, int unsorted,
	int fixed_depth)
{
	std::ifstream in (inname);
	if (!in)
		fileerror (inname);

	std::ofstream out (outname);
	if (!out)
		fileerror (outname, "create");

        // if the file starts with a digit, it is in the bitcode format
        ignorecomments (in);
        if ((in. peek () >= '0') && (in. peek () <= '9'))
	{
		sout << "Converting a bitcode file to a list of cubes.\n";
		pointset p;
		if (readbitpoints (in, p, 0) < 0)
                        return -1;
                out << "; This is a set of points read from '" <<
                        inname << "'.\n";
                out << p;
        }
        // otherwise the file is in the list-of-cubes format
        else
        {
		sout << "Converting a list of cubes to a bitcode file.\n";
                pointset p;
                in >> p;
		if (!p. empty ())
		{
			coordinate *zero = new coordinate [p. dimension ()];
			for (int i = 0; i < p. dimension (); i ++)
				zero [i] = 0;
			if (writebitpoints (out, p, !unsorted, fixed_depth,
				(fixed_depth >= 0) ? zero : NULL) < 0)
	                        return -1;
			delete [] zero;
		}
		else
			sout << "There are no points. Writing nothing.\n";
        }

        return 0;
} /* bitcode2pointset */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare the parameters of the program
	char *inname = NULL, *outname = NULL;
	int unsorted = 0;
	int fixed_depth = -1;

	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	argswitch (a, "u", unsorted, 1);
	arg (a, "f", fixed_depth, 0);
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
		bitcode2pointset (inname, outname, unsorted, fixed_depth);
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
		sout << "ABORT: An unknown error occurred." << '\n';
		return -1;
	}
} /* main */

/// @}

