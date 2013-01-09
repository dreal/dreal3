/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file psetcomm.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on May 7, 2000. Last revision: November 23, 2002.


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
#include <ctime>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
PointSetCommonPart, ver. 0.02. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo ="\
Call with: X1.cub ... Xn.cub outfile.cub [-q].\n\
The program computes the common part of the sets of points X1 ... Xn\n\
and saves the result to the output file.\n\
Hint: The first set is kept in the memory, and the other sets are only\n\
read through, so it is wise to put the smallest set at the beginning.\n\
Switches and additional arguments:\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";

#define MAXNAMES 200

#ifndef MAXDIM
#define MAXDIM 64
#endif


// --------------------------------------------------
// --------------------- TOOLS ----------------------
// --------------------------------------------------

int eof_or_brace (int ch)
{
	switch (ch)
	{
		case EOF:
		case 40:	// left parenthesis
		case 91:	// left bracket
		case 123:	// left brace
			return 1;
		default:
			return 0;
	}
} /* eof_or_brace */


// --------------------------------------------------
// -------------------- PSETCOMM --------------------
// --------------------------------------------------

int psetcomm (char *names [], int namecount, char *outname)
// Return: 0 = Ok, -1 = Error.
{
	pointset *p;

	// read the first set of points
	{
		sout << "Reading '" << names [0] << "'... ";
		std::ifstream f (names [0]);
		if (!f)
			fileerror (names [0]);
		p = new pointset;
		f >> *p;
		sout << p -> size () << " points read.\n";
	}

	// check if the dimension is not too high
	int dim = p -> dimension ();
	if (dim >= MAXDIM)
		throw "The dimension of the points is too high.";

	// read the other sets of points and compute the common part
	coordinate point [MAXDIM];
	for (int name = 1; name < namecount; name ++)
	{
		// say you are going to read a file
		sout << "Reading '" << names [name] << "'... ";

		// open the file to read points from
		std::ifstream f (names [name]);
		if (!f)
			fileerror (names [name]);

		// create a new set of points
		pointset *q = new pointset;
		if (!q)
			throw "Not enough memory for the set of points.";

		// inherit the previous creation time
		if ((q -> stat) && (p -> stat))
			q -> stat -> creationtime = p -> stat -> creationtime;

		// prepare a counter of points in the set
		int count = 0;

		// read until the end of the file
		ignorecomments (f);
		while (f. peek () != EOF)
		{
			// if this is not an opening parenthesis, ignore it
			if (closingparenthesis (f. peek ()) == EOF)
			{
				ignoreline (f);
				ignorecomments (f);
				continue;
			}

			// read a point
			int n = read (f, point, MAXDIM);
			ignorecomments (f);

			// verify if the dimension is the same
			if (!dim)
				dim = n;
			else if (dim != n)
				throw "Not the same dimension.";

			// check if the dimension is not too high
			if (n >= MAXDIM)
				throw "The dimension is much too high.";

			// if this point is in the previous set,
			// add it to the newly created set
			if (p -> check (point))
			{
				p -> remove (point);
				q -> add (point);
			}

			// increase the point counter
			count ++;
		}

		// replace the previous set of points with the new one
		delete p;
		p = q;

		// display a message how many points were analyzed
		sout << count << " analyzed, " << p -> size () << " remained.\n";
	}

	// say you are writing the result to an output file
	sout << "Writing the result to '" << outname << "'... ";

	// open a file to write the common part to
	std::ofstream out (outname);
	if (!out)
		fileerror (outname, "create");

	// go through the set of points and write the common part
	out << "; This is the common part of the following sets:\n";
	for (int j = 0; j < namecount; j ++)
		out << ";\t" << names [j] << '\n';

	// write the resulting set of points if it was not being written
	out << *p;

	sout << "Done.\n";

	delete p;
	return 0;
} /* common part */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong parameters.
{
	// prepare user-configurable data
	char *names [MAXNAMES], *outname = NULL;
	int count = 0;

	// analyze the command line
	arguments a;
	arg (a, NULL, names, count, MAXNAMES);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// correct the arguments
	if (count > 1)
		outname = names [-- count];

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

	// try running the main function and catch an error message if thrown
	try
	{
		psetcomm (names, count, outname);
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

