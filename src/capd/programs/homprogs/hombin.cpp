/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file hombin.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 29, 2005. Last revision: December 3, 2005.


#include "capd/homology/homology.h"

#include <exception>
#include <cstdlib>
#include <new>
#include <iostream>
#include <fstream>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
HomBinCube, ver. 0.02. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: file.bin -d dim -s size\n\
This program computes the homology of a full cubical set which is a subset\n\
of a large cube, and is encoded in the binary format in an input file.\n\
Note: The dimension may be limited to 3 in this version of the program.\n\
Optional arguments:\n\
-p p - compute the homology over Z modulo p instead of Z,\n\
-s size - the size of the edge of the big binary cube (a power of 2),\n\
-d dim - the dimension of the cubes (not all dimensions are supported),\n\
-w wrap - set space wrapping; repeat for each axis, 0 - no wrapping,\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// --------------------- HOMBIN ---------------------
// --------------------------------------------------

template <int dim, int twoPower>
void hombin (const char *Xname)
{
	// read the data from the input file
	std::ifstream in;
	in. open (Xname, std::ios::in | std::ios::binary);
	if (!in)
		fileerror (Xname);
	char *buf = new char [1 << (dim * twoPower - 3)];
	in. read (buf, 1 << (dim * twoPower - 3));
	in. close ();

	int betti [dim + 1];
	ComputeBettiNumbers<dim,twoPower> (buf, betti,
		PointBase::getwrapping (dim));

	delete [] buf;
	return;
} /* hombin */

typedef void (*function) (const char *Xname);
typedef struct
{
	int dim;
	int twoPower;
	function f;
} ftabelement;

ftabelement ftab [] =
{
/*	{1, 3, hombin<1,3>}, {1, 4, hombin<1,4>},
	{1, 5, hombin<1,5>}, {1, 6, hombin<1,6>},
	{1, 7, hombin<1,7>}, {1, 8, hombin<1,8>},
	{1, 9, hombin<1,9>}, {1, 10, hombin<1,10>},
	{1, 11, hombin<1,11>}, {1, 12, hombin<1,12>},
	{1, 13, hombin<1,13>}, {1, 14, hombin<1,14>},
	{1, 15, hombin<1,15>}, {1, 16, hombin<1,16>},
	{1, 17, hombin<1,17>}, {1, 18, hombin<1,18>},
	{1, 19, hombin<1,19>}, {1, 20, hombin<1,20>},
	{1, 21, hombin<1,21>}, {1, 22, hombin<1,22>},
	{1, 23, hombin<1,23>}, {1, 24, hombin<1,24>},

	{2, 3, hombin<2,3>}, {2, 4, hombin<2,4>},
	{2, 5, hombin<2,5>}, {2, 6, hombin<2,6>},
*/	{2, 7, hombin<2,7>}, {2, 8, hombin<2,8>},
/*	{2, 9, hombin<2,9>}, {2, 10, hombin<2,10>},
	{2, 11, hombin<2,11>}, {2, 12, hombin<2,12>},
	{2, 13, hombin<2,13>}, {2, 14, hombin<2,14>},
	{2, 15, hombin<2,15>},

	{3, 3, hombin<3,3>}, {3, 4, hombin<3,4>},
	{3, 5, hombin<3,5>}, {3, 6, hombin<3,6>},
*/	{3, 7, hombin<3,7>}, {3, 8, hombin<3,8>},
/*	{3, 9, hombin<3,9>}, {3, 10, hombin<3,10>},

	{4, 3, hombin<4,3>}, {4, 4, hombin<4,4>},
	{4, 5, hombin<4,5>}, {4, 6, hombin<4,6>},
	{4, 7, hombin<4,7>},

	{5, 3, hombin<5,3>}, {5, 4, hombin<5,4>},
	{5, 5, hombin<5,5>}, {5, 6, hombin<5,6>},

	{6, 3, hombin<5,3>}, {6, 4, hombin<5,4>},
	{6, 5, hombin<5,5>},

	{7, 3, hombin<7,3>}, {7, 4, hombin<7,4>},

	{8, 3, hombin<8,3>},

	{9, 3, hombin<9,3>},

	{10, 3, hombin<10,3>},
*/
	{0, 0, 0}
};

void hombin (const char *Xname, int size, int dim)
{
	// determine the power of two
	int twoPower = 3;
	while (size > (1 << twoPower))
		twoPower ++;
	if (size != (1 << twoPower))
		throw "The size of the big cube must be a power of 2.";

	// run the appropriate function to continue the computations
	ftabelement *fe = ftab;
	while (fe -> f)
	{
		if ((fe -> dim == dim) && (fe -> twoPower == twoPower))
		{
			sout << "Note: Space dimension = " << dim <<
				", cube size = " << (1 << twoPower) <<
				" (2^" << twoPower << ").\n";
			return fe -> f (Xname);
		}
		++ fe;
	}
	sout << "SORRY, the program does not support dimension " << dim <<
		" and cube size " << (1 << twoPower) <<
		" (2^" << twoPower << ").\n";
	sout << "The following configurations of dimension and cube size "
		"are supported:\n";
	fe = ftab;
	int count = 0;
	while (fe -> f)
	{
		if (count && !(count % 6))
			sout << "\n";
		sout << "(" << fe -> dim << "," <<
			(1 << fe -> twoPower) << ") ";
		++ fe;
		++ count;
	}
	sout << "\n";
	sout << "Note that the cube size must be a power of 2.\n";
	sout << "To support other configurations, "
		"the program must be recompiled.\n";
	return;
} /* hombin */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *Xname = NULL;
	int p = 0, size = 0, dim = 0;
	coordinate wrap [Cube::MaxDim];
	for (int i = 0; i < Cube::MaxDim; ++ i)
		wrap [i] = 0;
	int wrapcount = 0;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, Xname);
	arg (a, "p", p);
	arg (a, "s", size);
	arg (a, "d", dim);
	arg (a, "w", wrap, wrapcount, Cube::MaxDim);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// if there are not enough file names, help should be displayed
	if (!Xname || (size <= 0) || (dim <= 0))
		argresult = 1;

	// set the requested ring of coefficients if different from Z
	if (p > 0)
		integer::initialize (p);

	// set the space wrapping if necessary
	if (wrapcount == 1)
		PointBase::setwrapping (wrap [0]);
	else if (wrapcount)
		PointBase::setwrapping (wrap);

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
		program_time = 1;

		// run the main procedure
		hombin (Xname, size, dim);

		// set an appropriate program time message
		program_time = "Total time used:";

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

