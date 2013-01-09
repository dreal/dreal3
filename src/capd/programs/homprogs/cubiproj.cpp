/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubiproj.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on March 4, 2003. Last revision: October 13, 2004.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/cubmaps.h"
#include "capd/homology/cubisets.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"

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
CUBIPROJ, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: graph.cel y.cel graph.chn y.chn q.chm [p.chm].\n\
This program creates the chain complex of the set of cubical cells\n\
which form the graph of the map F, the chain complex of Y and the chain\n\
map of the projection from the graph of F onto F's codomain Y.\n\
If 'p.chn' is specified, the chain map of the projection from the graph\n\
to the map's domain composed with the inclusion into Y is created, too.\n\
Optional arguments:\n\
-w n - wrap space every 'n' units (repeat for each axis separately),\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// --------------------- TOOLS ----------------------
// --------------------------------------------------
// small procedures, often copied from other programs

static void readcells (const char *name, cubicalcomplex &cel,
	const char *what)
// Read a cubical complex from the given file.
// Based on "readcells" from "homcubes.cpp".
{
	if (!name)
		return;
	sout << "Reading cells ";
	if (what)
		sout << "to " << what << ' ';
	sout << "from '" << name << "'... ";
	std::ifstream in (name);
	if (!in)
		fileerror (name);

	// ignore all the introductory data
	ignorecomments (in);
	while (!!in && closingparenthesis (in. peek ()) == EOF)
	{
		ignoreline (in);
		ignorecomments (in);
	}

	// read the cells
	int_t prev = cel. size ();
	in >> cel;
	sout << (cel. size () - prev) << " cells read.\n";
	return;
} /* readcells */

static void writechaincomplex (const char *name, const cubicalcomplex &g,
	const char *what)
// Write the algebraic chain complex of the given cubical complex.
// Boundary formulas are restricted to cells which are in the cub. complex.
// Based on "createchaincomplex" from "gcomplex.h".
{
	// create the output file
	std::ofstream out (name);
	if (!out)
		fileerror (name, "create");

	// say what you are doing
	sout << "Writing the chain complex of " << what <<
		" to '" << name << "'... ";

	// write the initial data
	out << "chain complex\n";
	out << "max dimension " << g. dim () << "\n";

	// write the data for each dimension separately
	out << "dimension 0: " << g [0]. size () << "\n";
	for (int d = 1; d <= g. dim (); d ++)
	{
		out << "dimension " << d << ": " << g [d]. size () << "\n";
		for (int_t i = 0; i < g [d]. size (); i ++)
		{
			int_t len = boundarylength (g [d] [i]);
			bool nothing = true;
			for (int_t j = 0; j < len; j ++)
			{
				// take the j-th boundary cell
				qcell thecell = boundarycell (g [d] [i], j,
					true);

				// if the cell is not there, skip it
				if ((thecell == g [d] [i]) ||
					(!g. check (thecell)))
					continue;

				// write the beginning of boundary if necess.
				if (nothing)
					out << "\t# " << (i + 1) << " = ";

				// determine the coefficient
				int coef = boundarycoef (g [d] [i], j);

				// write the appropariate coefficient
				if (coef == 1)
					if (nothing);
					else
						out << " + ";
				else if (-coef == 1)
					if (nothing)
						out << "-";
					else
						out << " - ";
				else
					out << " + " << coef <<
						" * ";

				// write the boundary cell number
				out << (g [d - 1]. getnumber (thecell) + 1);

				// indicate that there was something
				nothing = false;
			}

			// end the line if there was something written
			if (!nothing)
				out << '\n';
		}

		// show a progress indicator
		if (d < g. dim ())
			scon << '.';
		else
			scon << ". ";
	}

	// finalize
	sout << "Done.\n";
	return;
} /* writechaincomplex */

void writeprojection (const char *name, const cubicalcomplex &Fcompl,
	const cubicalcomplex &Ycompl, int offset, int outdim, int discarddim,
	int *level, const char *what)
// Write the chain map of the projection from the cell complex of the graph
// of a map to the cell complex of the codomain of the map.
// If a table of levels is given, create the map only at given levels.
// Based on "createprojection" from "cubisets.h".
{
	// if no file name is given, ignore it
	if (!name || !*name)
		return;

	// create the output file
	std::ofstream out (name);
	if (!out)
		fileerror (name, "create");

	// say what you are doing
	sout << "Writing the chain map of " << what <<
		" to '" << name << "'... ";

	// write the initial data
	out << "chain map\n";

	// go through the list of all the dimensions which are of concern
	for (int d = 0; d <= Ycompl. dim (); d ++)
		if ((!level || level [d]) && (Fcompl. dim () >= d))
		{
			// take sets of cells of this dimension
			const hashedset<qcell> &Fset = Fcompl [d];
			if (Fset. empty ())
				continue;
			const hashedset<qcell> &Yset = Ycompl [d];
			if (Yset. empty ())
				continue;

			// write the current dimension
			out << "dimension " << d << "\n";

			// go through the list of cells in Fcompl of dim. d
			for (int_t i = 0; i < Fset. size (); i ++)
			{
				// get this cell and its coordinates
				const qcell &Fcell = Fset [i];
				coordinate left [qcell::MaxDim];
				Fcell. leftcoord (left);
				coordinate right [qcell::MaxDim];
				Fcell. rightcoord (right);

				// check if this cell has no width in the
				// directions that are discarded
				register int j;
				for (j = 0; j < offset; j ++)
					if (left [j] != right [j])
					{
						j = offset + 33;
						break;
					}
				if (j > offset)
					continue;
				for (j = 0; j < discarddim; j ++)
					if (left [offset + outdim + j] !=
						right [offset + outdim + j])
					{
						j = discarddim + 33;
						break;
					}
				if (j > discarddim)
					continue;

				// create the projected cell
				if (!(PointBase::check (left + offset, outdim)))
					continue;
				if (!(PointBase::check (right + offset, outdim)))
					continue;
				qcell projected (left + offset,
					right + offset, outdim);

				// find its number in Y
				int_t nr = Yset. getnumber (projected);

				// if not found, discard it
				if (nr < 0)
					continue;

				// add the pair to the projection map
				out << "\t# " << (i + 1) << " = " <<
					(nr + 1) << '\n';
			}
		}

	// finalize
	sout << "Done.\n";
	return;
} /* createprojection */


// --------------------------------------------------
// -------------------- CUBIPR0J --------------------
// --------------------------------------------------

int cubiproj (const char *inFname, const char *inYname,
	const char *outFname, const char *outYname,
	const char *outQname, const char *outPname)
{
	// read the cubical complexes from the input files
	cubicalcomplex Fcompl, Ycompl;
	readcells (inFname, Fcompl, "the graph of F");
	readcells (inYname, Ycompl, "the codomain Y of F");

	// write the chain complexes to suitable files
	writechaincomplex (outFname, Fcompl, "the graph of F");
	writechaincomplex (outYname, Ycompl, "the codomain Y of F");

	// determine the dimension of the domain
	int dim = Ycompl. dim ();
	if (dim <= 0)
		dim = Fcompl. dim () / 2;

	// write the chain maps of the projections
	writeprojection (outQname, Fcompl, Ycompl, dim, dim, 0, NULL,
		"the projection q: F -> Y");
	writeprojection (outPname, Fcompl, Ycompl, 0, dim, dim, NULL,
		"the projection p: F -> X");

	return 0;
} /* cubiproj */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	char *inFname = NULL, *inYname = NULL, *outFname = NULL,
		*outYname = NULL, *outQname = NULL, *outPname = NULL;
	coordinate wrap [qcell::MaxDim];
	for (int i = 0; i < qcell::MaxDim; i ++)
		wrap [i] = 0;
	int wrapcount = 0;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, inFname);
	arg (a, NULL, inYname);
	arg (a, NULL, outFname);
	arg (a, NULL, outYname);
	arg (a, NULL, outQname);
	arg (a, NULL, outPname);
	arg (a, "w", wrap, wrapcount, qcell::MaxDim);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

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

	// if help requested or no filenames present, show help information
	if (!outQname || (argresult > 0))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		cubiproj (inFname, inYname, outFname, outYname, outQname,
			outPname);
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

