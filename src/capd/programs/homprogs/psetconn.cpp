/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file psetconn.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on February 2, 2001. Last revision: November 24, 2002.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <new>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <cstdlib>
#include <ctime>
#include <sstream>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
Connected Comp., ver. 0.02. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo ="\
Call with: infile.cub [outname].\n\
The program divides the set of points stored in the input file\n\
into separate connected components and saves these components\n\
to the output files whose names are created from the name given\n\
by appending the components' numbers and the extension '.cub' to it.\n\
Switches and additional arguments:\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// -------------------- PSETCONN --------------------
// --------------------------------------------------

void moveset (pointset &p, const pointset &q)
{
	for (int_t i = 0; i < q. size (); i ++)
		p. add (q [i]);
	return;
} /* moveset */

int connectedcomponents (char *inname, char *outname)
// Return: 0 = Ok, -1 = Error.
{
	// read the set of points
	sout << "Reading '" << inname << "'... ";
	pointset p;
	{
		std::ifstream in (inname);
		if (!in)
			fileerror (inname);
		in >> p;
	}
	sout << p. size () << " points read.\n";

	// if the set is empty, finish here
	if (p. empty ())
	{
		sout << "The set is empty.\n";
		return 0;
	}

	// prepare the connected components to extract
	multitable<pointset *> q;

	int components = 0, maxused = 0;
	int count = 0;

	sout << "Computing... ";

	while (!p. empty ())
	{
		coordinate *c = p [p. size () - 1];
		int found = -1;
		for (int i = 0; i < components; i ++)
		{
			if (countneighbors (*(q (i)), c, INSIDE, 1))
			{
				if (found < 0)
				{
					q [i] -> add (c);
					found = i;
				}
				else
				{
					moveset (*(q [found]), *(q (i)));
					delete (q [i]);
					for (int j = i + 1;
						j < components; j ++)
						q [j - 1] = q (j);
					components --;
				}
			}
		}
		if (found < 0)
		{
			q [components] = new pointset;
			q [components] -> add (c);
			components ++;
			if (components > maxused)
				maxused = components;
		}
		p. remove (c);

		if (!((++ count) % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
	}

	// indicate the result
	sout << maxused << " intermediate sets of points were used.\n";
	if (components == 1)
		sout << "The set is connected.\n";
	else
		sout << "The set contains " << components <<
			" connected components.\n";

	// if there is no need to save these components, then finish here
	if (!outname)
		return 0;

	// say that you are writing the result to output files
	sout << "Writing the result... ";

	// write the components to the output file
	for (int c = 0; c < components; c ++)
	{
		// prepare a file name for this component
		std::ostringstream s;
		s << outname;
		for (int digit = 10000; digit > 1; digit /= 10)
			if (((c + 1) < digit) && (components >= digit))
				s << '0';
		s << (c + 1) << ".cub";
		const char *name = s. str (). c_str ();

		// open a file to write the components to
		std::ofstream out (name);
		if (!out)
			fileerror (name, "create");

		out << "; This is the connected component no. " << (c + 1) <<
			" of '" << inname << "'.\ndimension " << 
			p. dimension () << '\n';
		for (int_t i = 0; i < q [c] -> size (); i ++)
		{
			write (out, (*(q [c])) [i], p. dimension ());
			out << '\n';
		}
		delete (q [c]);
	}

	sout << "Done.\n";

	return 0;
} /* connected components */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *inname = NULL, *outname = NULL;

	arguments a;
	arg (a, NULL, inname);
	arg (a, NULL, outname);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's title
	if (argresult >= 0)
		sout << title << '\n';

	// if not enough file names, help should be displayed
	if (!inname)
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
		connectedcomponents (inname, outname);
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

