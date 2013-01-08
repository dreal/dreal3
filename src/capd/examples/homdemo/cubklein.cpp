/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubklein.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on October 28, 2003. Last revision: March 30, 2005.


#include "capd/homology/homology.h"

#include <exception>
#include <cstdlib>
#include <math.h>
#include <new>
#include <iostream>
#include <fstream>

using namespace capd::homology;

const double pi = 3.14159265358979323846;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CUBKLEIN, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: filename.cub.\n\
This is a demonstration program which creates a set of cubes that is\n\
supposed to be an approximation of a Klein bottle in R^4.\n\
Optional arguments:\n\
-r N - set the inner radius of the Klein bottle (default: 2),\n\
-R N - set the outer radius of the Klein bottle (default: 4),\n\
-s N - set the number of inner iteration steps (default: 13 times r),\n\
-S N - set the number of outer iteration steps (default: 13 times R),\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// ---------------------- DEMO ----------------------
// --------------------------------------------------

static void KleinBottle (const char *filename, int radius, int Radius,
	int steps, int Steps)
// Draw a cubical approximation of a Klein bottle and save it to the file.
{
	// say what is going to be done
	sout << "Drawing: r = " << radius << " (" << steps <<
		" steps), R = " << Radius << " (" << Steps << " steps)... ";

	// create a set of points (cubes) and fix its dimension
	pointset p;
	p. dimension (4);

	// draw all the points ('a' iterates 'alpha', 'b' iterates 'beta')
	double x [4];
	for (int a = 0; a < Steps; a ++)
	{
		double alfa = 2 * pi * a / Steps;
		for (int b = 0; b < steps; b ++)
		{
			double beta = 2 * pi * b / steps;

			// compute the coordinates of the point
			x [0] = (Radius * cos (alfa) +
				radius * cos (alfa) * cos (alfa / 2) *
				cos (beta));
			x [1] = (Radius * sin (alfa) +
				radius * sin (alfa) * cos (alfa / 2) *
				cos (beta));
			x [2] = (radius * sin (alfa / 2) * cos (beta));
			x [3] = (radius * sin (beta));

			// add the cube containing this point to the set
			p. add (x);
		}

		// show a progress indicator
		if (!(a % 373))
			sout << std::setw (10) << a <<
				"\b\b\b\b\b\b\b\b\b\b";
	}
	sout << p. size () << " cubes.\n";
	
	// write the set of cubes to a file
	sout << "Saving the cubes to '" << filename << "'... ";
	std::ofstream out (filename);
	if (!out)
		fileerror (filename, "create");
	out << p;
	sout << "Done.\n";

	return;
} /* KleinBottle */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *filename = NULL;
	int radius = 2;
	int Radius = 4;
	int steps = 0;
	int Steps = 0;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, filename);
	arg (a, "r", radius);
	arg (a, "R", Radius);
	arg (a, "s", steps);
	arg (a, "S", Steps);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// adjust the numbers of steps if not defined
	if (steps <= 0)
		steps = 13 * radius;
	if (Steps <= 0)
		Steps = 13 * Radius;
		
	// if there is no file name given, help should be displayed
	if (!filename)
		argresult = 1;

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested, show help information
	if (argresult > 0)
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		// set an appropriate program time message
		program_time = "Aborted after:";

		// run the main procedure
		KleinBottle (filename, radius, Radius, steps, Steps);

		// set an appropriate program time message and turn it on
		program_time = "Total time used:";
		program_time = 1;

		// finalize
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

