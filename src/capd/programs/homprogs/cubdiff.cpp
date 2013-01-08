/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubdiff.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on April 21, 1999. Last revision: January 20, 2005.

// Former name(s) of this program: PSETDIFF.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/cubisets.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

#include <exception>
#include <cstdlib>
#include <ctime>
#include <new>
#include <iostream>
#include <fstream>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

const char *title = "\
CUBDIFF, ver. 0.04. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo ="\
Call with: X.cub Y.cub Z.cub [-x | -y].\n\
The program computes X\\Y and saves it to 'Z.cub'.\n\
The sets X and Y can contain either cubes or cubical cells.\n\
Parameters:\n\
-x - keep the set X in the memory (recommended if X is bigger than Y),\n\
-y - keep Y in the memory (default; preserves the order of elements),\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// -------------------- CUBDIFF ---------------------
// --------------------------------------------------

template <class output>
inline output &write (output &out, int countcubes, int countcells,
	bool capital)
{
	if (countcubes)
		out << countcubes << " cube" <<
			((countcubes > 1) ? "s" : "");
	if (countcells)
		out << (countcubes ? " and " : "") << countcells <<
			" cell" << ((countcells > 1) ? "s" : "");
	if (!countcubes && !countcells)
		out << (capital ? "Nothing" : "nothing");
	return out;
} /* write */

int readfile (const char *name, pointset &p, cubicalcomplex &q,
	const char *what)
{
	// say what you are doing
	sout << "Reading " << what << " from '" << name << "'... ";

	// open the file
	std::ifstream in (name);
	if (!in)
		fileerror (name);

	// read the cubes and/or cells
	int dim = 0;
	while (in. peek () != EOF)
	{
		// read a cube or a cell from the input file
		coordinate left [qcell::MaxDim], right [qcell::MaxDim];
		int type;
		int d = readcubeorcell (in, left, right, qcell::MaxDim,
			&type);

		// if nothing read, quit the loop
		if (d <= 0)
			break;

		// verify the dimension and set it if necessary
		if ((dim > 0) && (d != dim))
			throw "Inconsistent space dimension.";
		else if (!dim)
		{
			dim = d;
			p. dimension (dim);
		}

		// add the object to the appropriate set
		if (type == CUBE)
			p. add (left);
		else
			q. add (qcell (left, right, dim));
	}

	// say how many of what has been read
	write (sout, p. size (), q. size (), true) << " read.\n";
	return 0;
} /* readfile */

int cubdiff (const char *xname, const char *yname, const char *outname,
	bool keepX)
{
	pointset p;
	cubicalcomplex q;

	// read the first set that has to be stored in memory
	readfile (keepX ? xname : yname, p, q, (keepX ? "X" : "Y"));

	// open the file to read through
	const char *name = keepX ? yname : xname;
	sout << "Reading through " << (keepX ? 'Y' : 'X') <<
		" from '" << name << "'... ";
	std::ifstream in (name);
	if (!in && (!keepX || !p. empty ()))
		fileerror (name);

	// create a file to write the difference of the sets of points to
	std::ofstream out (outname);
	if (!out)
		fileerror (outname, "create");
	out << "; This is the set difference: '" << xname <<
		"' \\ '" << yname << "'.\n";

	// determine the dimension if it is known or set 'dim' to zero
	int dim = p. empty () ? 0 : p. dimension ();

	// go through the set stored in the file and compute the difference
	int countreadcubes = 0, countreadcells = 0;
	int countwrittencubes = 0, countwrittencells = 0;
	ignorecomments (in);
	while (in && (!keepX || p. size () || !q. empty ()))
	{
		// read a cube or cell from the file
		coordinate left [qcell::MaxDim], right [qcell::MaxDim];
		int type;
		int d = readcubeorcell (in, left, right, qcell::MaxDim,
			&type);
		if (!d)
			break;
		if (type == CUBE)
			countreadcubes ++;
		else
			countreadcells ++;

		// verify the dimension and set it if necessary
		if ((dim > 0) && (d != dim))
		{
			out << "\n; *** AN ERROR OCCURRED ***\n";
			throw "Inconsistent space dimension.";
		}
		else if (!dim)
			dim = d;

		// if X is kept in the memory, remove the cube/cell from X
		if (keepX)
		{
			if (type == CUBE)
				p. remove (left);
			else if (PointBase::check (left, dim) &&
				PointBase::check (right, dim))
				q. remove (qcell (left, right, dim));
		}
		// otherwise copy the cube if it is not in Y
		else if ((type == CUBE) && !p. check (left))
		{
			write (out, left, dim);
			out << '\n';
			countwrittencubes ++;
		}
		// or copy the cell if it is not in Y
		else if ((type == CELL) && (!PointBase::check (left, dim) ||
			!PointBase::check (right, dim) ||
			!q. check (qcell (left, right, dim))))
		{
			out << '[';
			write (out, left, dim);
			out << ' ';
			write (out, right, dim);
			out << "]\n";
			countwrittencells ++;
		}

		// show progress indicator
		int count = countreadcubes + countreadcells;
		if (!(count % 4373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
	}

	// indicate how many cubes and/or cells have been analyzed
	write (sout, countreadcubes, countreadcells, true) << " analyzed.\n";

	// write the resulting set if it was not being written
	if (keepX)
	{
		// put the information on what the set contains in the set
		out << "; The set contains ";
		write (out, p. size (), q. size (), false) << ".\n";

		// write all the cubes to the file
		if (!p. empty ())
		{
			sout << "Writing " << p. size () << " cubes "
				"from X\\Y to '" << outname << "'... ";
			out << p;
			sout << "Done.\n";
		}

		// write all the cubical cells to the file
		if (!q. empty ())
		{
			sout << "Writing " << q. size () << " cells "
				"from X\\Y to '" << outname << "'... ";
			out << q;
			sout << "Done.\n";
		}

		// say how much of what has been written
		write (sout, p. size (), q. size (), true) <<
			" written to '" << outname << "'.\n";
	}
	// otherwise indicate the number of cubes and/or cells it contains
	else
	{
		// put the information on what the set contains in the set
		out << "; The set contains ";
		write (out, countwrittencubes, countwrittencells, false) <<
			".\n";

		// say how much of what has been written
		write (sout, countwrittencubes, countwrittencells, true) <<
			" written to '" << outname << "'.\n";
	}

	return 0;
} /* cubdiff */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong parameters.
{
	// prepare user-configurable data
	char *xname = NULL, *yname = NULL, *outname = NULL;
	bool keepX = false;

	// analyze the command line
	arguments a;
	arg (a, NULL, xname);
	arg (a, NULL, yname);
	arg (a, NULL, outname);
	argswitch (a, "x", keepX, true);
	argswitch (a, "y", keepX, false);
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
	if (!outname || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		cubdiff (xname, yname, outname, keepX);
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

