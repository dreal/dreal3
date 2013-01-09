/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file homcelmp.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on May 18, 2005. Last revision: May 18, 2005.


#include "capd/homology/homology.h"

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
HomCellMaps, ver. 0.01. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
Call with: F.map.\n\
This is a demonstration program which computes the homomorphism induced\n\
in homology by a given cubical multivalued map defined on cubical cells\n\
instead of full cubes. It does not support relative homology. It does no\n\
geometric reduction of the cubical sets, but creates a full graph of the\n\
map, and may therefore be quite inefficient. Written for Natalia Zaremba.\n\
Optional arguments:\n\
-p p - compute the homology over Z modulo p instead of plain Z,\n\
-i - compose the map with the inverse of the homom. ind. by the inclusion,\n\
-h - display this brief help information only and exit.\n\
For more information ask the author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// ---------------------- DEMO ----------------------
// --------------------------------------------------

void demo (const char *Fname, const char *Yname, bool inclusion, int p)
{
	// add an empty line for clearer output
	sout << '\n';

	// set the requested ring of coefficients if different from Z
	if (p > 0)
		integer::initialize (p);

	// read the map from a file
	sout << "Reading a cell map from '" << Fname << "'... ";
	mvmap<qcell,qcell> Fmap;
	{
		std::ifstream in (Fname);
		if (!in)
			fileerror (Fname);
		in >> Fmap;
	}
	sout << Fmap. getdomain (). size () << " assignments.\n";

	// determine the codomain of the map (read from file or the image)
	gcomplex<qcell,integer> Ycompl;
	if (Yname && *Yname)
	{
		sout << "Reading the codomain from '" << Yname << "... ";
		std::ifstream in (Yname);
		if (!in)
			fileerror (Yname);
		in >> Ycompl;
	}
	else
	{
		sout << "Determining the range of the map... ";
		const hashedset<qcell> &domain = Fmap. getdomain ();
		for (int_t i = 0; i < domain. size (); ++ i)
			Ycompl. add (Fmap (i));
	}
	sout << Ycompl. size () << " cells.\n";

	// determine the space dimension
	int dim = Ycompl [Ycompl. dim ()] [0]. spacedim ();
	sout << "The space dimension is " << dim << ".\n";

	// make Y be a full geometric complex
	sout << "Adding boundaries in the codomain... ";
	int_t prevY = Ycompl. size ();
	Ycompl. addboundaries ();
	sout << (Ycompl. size () - prevY) << " cells added.\n";

	// create map's graph
	sout << "Creating a geometric complex of the graph of the map... ";
	gcomplex<qcell,integer> Fcompl;
	creategraph (Fmap, Fcompl);
	sout << "Done.\n";

	// make the graph be a full geometric complex
	sout << "Adding boundaries in the graph... ";
	int_t prevF = Fcompl. size ();
	Fcompl. addboundaries ();
	sout << (Fcompl. size () - prevF) << " cells added.\n";

	// create a chain complex from the graph of F
	chaincomplex<integer> cgraph (Fcompl. dim (), false);
	sout << "Creating the chain complex of the graph of F... ";
	createchaincomplex (cgraph, Fcompl);
	sout << "Done.\n";

	// create the chain complex from Y
	chaincomplex<integer> cy (Ycompl. dim (), false);
	sout << "Creating the chain complex of Y... ";
	createchaincomplex (cy, Ycompl);
	sout << "Done.\n";

	// create the projection map from the graph of the map to Y
	chainmap<integer> cmap (cgraph, cy);
	sout << "Creating the chain map of the projection... ";
	createprojection (Fcompl, Ycompl, cmap, dim, dim, 0);
	sout << "Done.\n";

	// create the projection map onto X composed with the inclusion X->Y
	chainmap<integer> imap (cgraph, cy);
	if (inclusion)
	{
		sout << "Creating the chain map of the inclusion... ";
		createprojection (Fcompl, Ycompl, imap, 0, dim, dim);
		sout << "Done.\n";
	}

	// compute the homology of the graph of the map
	chain<integer> *hom_cx;
	int maxlevel_cx = Homology (cgraph, "the graph of the map", hom_cx);

	// compute the homology of the codomain of the map
	chain<integer> *hom_cy;
	int maxlevel_cy = Homology (cy, "the codomain of the map", hom_cy);

	// prepare the data structures for the homology
	chaincomplex<integer> hgraph (maxlevel_cx);
	chaincomplex<integer> hy (maxlevel_cy);
	chainmap<integer> hmap (hgraph, hy);
	chainmap<integer> hincl (hgraph, hy);
	chainmap<integer> hcomp (hy, hy);

	// show the map induced in homology by the chain map
	sout << "The map induced in homology is as follows:\n";
	hgraph. take_homology (hom_cx);
	hy. take_homology (hom_cy);
	hmap. take_homology (cmap, hom_cx, hom_cy);
	hmap. show (sout, "\tf", "x", "y");

	// invert the inclusion homomorphism and show the result
	if (inclusion)
	{
		sout << "The map induced in homology by the inclusion:\n";
		hincl. take_homology (imap, hom_cx, hom_cy);
		hincl. show (sout, "\ti", "x", "y");

		sout << "The inverse of the map induced by the inclusion:\n";
		try
		{
			hincl. invert ();
			hincl. show (sout, "\tI", "y", "x");
			sout << "The composition of F and the inverse "
				"of the map induced by the inclusion:\n";
			hcomp. compose (hmap, hincl);
			hcomp. show (sout, "\tF", "y", "y");
		}
		catch (...)
		{
			sout << "Oh, my goodness! This map is apparently "
				"not invertible.\n";
		}
	}

	// clean up and quit
	delete [] hom_cx;
	delete [] hom_cy;
	return;
} /* demo */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// prepare user-configurable data
	char *Fname = NULL, *Yname = NULL;
	bool inclusion = false;
	int p = 0;

	// interprete the command-line arguments
	arguments a;
	arg (a, NULL, Fname);
	arg (a, NULL, Yname);
	arg (a, "p", p);
	argswitch (a, "i", inclusion, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's main title
	if (argresult >= 0)
		sout << title << '\n';

	// if there are not enough file names, help should be displayed
	if (!Fname)
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
		demo (Fname, Yname, inclusion, p);

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

