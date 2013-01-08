/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file homsimpl.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on March 12, 2003. Last revision: September 5, 2003 (Nov 9, 2004).


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
//#include "capd/homology/integer.h"
//#include "capd/homology/chains.h"
//#include "capd/homology/hashsets.h"
//#include "capd/homology/gcomplex.h"
//#include "capd/homology/simplex.h"
#include "capd/homology/homtools.h"

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
HOMSIMPL, ver. 0.01, 11/09/04. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
This program computes (relative) homology of simplicial complexes.\n\
Call with:\n\
X.sim [A.cub] - for homology computation of X or (X+A, A),\n\
Switches and additional arguments:\n\
-k file - keep these simplices in X (while reducing),\n\
-g file - save homology generators,\n\
-s prefix - save intermediate data; add the given prefix to file names,\n\
-l n - compute only this homology level,\n\
-b file - save Betti numbers to a file, one per line, including zeros,\n\
-p n - perform the computations in the field of integers modulo prime n,\n\
-r n - run only these stages: 1: collapse simplices, 2: create the chain\n\
       complex of X or (X,A), 3: compute homology.\n\
-d - don't add faces to cells (assume missing simplices belong in A),\n\
-h - display this brief help information only and exit.\n\
Temporary switches (for debug and tests; will be removed or changed soon):\n\
-C - don't collapse faces.\n\
For more information consult the accompanying documentation (if available)\n\
or ask the program's author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// --------------------- TOOLS ----------------------
// --------------------------------------------------

static void save0betti (const char *bettiname)
{
	if (!bettiname || !*bettiname)
		return;
	std::ofstream out (bettiname);
	if (!out)
		sout << "WARNING: Cannot create '" << bettiname <<
			"' to output Betti numbers to.\n";
	else
		out << "0\n";
	return;
} /* save0betti */

static void savebetti (const char *bettiname, const chain<integer> *hom,
	int dim, int spacedim)
{
	if (!bettiname || !*bettiname)
		return;
	std::ofstream out (bettiname);
	if (!out)
	{
		sout << "WARNING: Cannot create '" << bettiname <<
			"' to output Betti numbers to.\n";
		return;
	}
	for (int i = 0; i <= dim; i ++)
	{
		int count = 0;
		for (int j = 0; j < hom [i]. size (); j ++)
			if (hom [i]. coef (j). delta () == 1)
				count ++;
		out << count << '\n';
	}
	for (int i = dim + 1; i < spacedim; i ++)
		out << "0\n";
	return;
} /* savebetti */

static int exithom (const char *message, const char *bettiname = NULL)
{
	sout << message << '\n';
	save0betti (bettiname);
	program_time = "Time used:";
	return 0;
} /* exithom */

static void savegenerators (const char *filename, const char *name,
	const chain<integer> *hom_cx, const chaincomplex<integer> &cx,
	const simplicialcomplex &Xcompl, int *level)
{
	if (!filename)
		return;
	sout << "Saving generators of " << name << " to '" << filename <<
		"'... ";
	std::ofstream out (filename);
	if (!out)
		fileerror (filename, "create");
	writegenerators (out, hom_cx, cx, Xcompl, level);
	sout << "Done.\n";
	return;
} /* savegenerators */


// --------------------------------------------------
// -------------------- HOMSIMPL --------------------
// --------------------------------------------------

enum runbitnames
{
	collapsebit = 0x01, chainbit = 0x02, hombit = 0x04
};

static int homsimpl (const char *Xname, const char *Aname,
	const char *keepname, const char *savefiles,
	const char *genname, const char *bettiname,
	int *level, bool dontaddfaces, bool dontcollapse, int runbits)
{
	// determine the minimal homology level of interest
	int minlevel = 0;
	while (level && !level [minlevel] && (minlevel < Simplex::MaxDim))
		minlevel ++;

	// ----- read the simplicial complexes -----

	// read the simplicial complex of X
	simplicialcomplex Xcompl;
	readcells (Xname, Xcompl, "X");

	// read the simplicial complex A
	simplicialcomplex Acompl;
	readcells (Aname, Acompl, "A");

	// remove from X simplices which are in A
	removeAfromX (Xcompl, Acompl, "X", "A");

	// if the set X is empty, no computations are necessary
	if (Xcompl. empty ())
	{
		if (!Acompl. empty ())
		{
			return exithom ("The set X is contained in A. "
				"The homology of (X,A) is trivial.\n",
				bettiname);
		}
		else
		{
			return exithom ("The set X is empty. "
				"The homology of X is trivial.", bettiname);
		}
	}

	// read cells to keep in X and A
	simplicialcomplex keepcompl;
	readcells (keepname, keepcompl, "simplices to keep");

	// determine the dimension of X and Y as simplicial complexes
	int Xorigdim = Xcompl. dim ();
	int Xdim = Xcompl. dim ();

	// set high homology levels to be ignored
	for (int i = Xdim + 1; level && (i < Simplex::MaxDim); i ++)
		level [i] = 0;

	// if the requested homology level is too large, the answer is simple
	if (minlevel > Xdim)
		return exithom ("The dimension of the set is lower "
			"than the requested homology level.");

	// ----- collapse the simplicial complex (X,A) -----

	// create a full cubical complex (with all the faces) of X\A
	if (dontcollapse)
	{
		// decrease the dimension of A to the dimension of X
		decreasedimension (Acompl, Xdim, "A");

		// add boundaries to cells in X and A
		if (!dontaddfaces)
			addboundaries (Xcompl, Acompl, minlevel, false,
				"X", "A");
	}

	// reduce the pair of sets (Xcells, Acells) while adding to them
	// boundaries of all the cells
	if (!dontcollapse)
	{
                collapse (Xcompl, Acompl, keepcompl, "X", "A",
			!dontaddfaces, false, true, level);

		// if nothing remains in X, then the result is trivial
		if (Xcompl. empty ())
			return exithom ("Nothing remains in X. "
				"The homology of (X,A) is trivial.\n",
				bettiname);
	}

	// forget the cells to keep in X
	if (!keepcompl. empty ())
	{
		simplicialcomplex empty;
		keepcompl = empty;
	}

	// make a correction to the dimension of X
	if (Xdim != Xcompl. dim ())
	{
		sout << "Note: The dimension of X decreased from " <<
			Xdim << " to " << Xcompl. dim () << ".\n";

		Xdim = Xcompl. dim ();
		for (int i = Xdim + 1; level && (i < Simplex::MaxDim); i ++)
			level [i] = 0;
	}

	// save the cells left in X and A after the reduction
	savetheset (Xcompl, savefiles, "x.sim", Aname ?
		"the simplices in X\\A after reduction" :
		"the simplices in X after reduction");
	if (Aname)
		savetheset (Acompl, savefiles, "a.sim",
			"the simplices in A after reduction");

	// if no more things have to be done, exit now
	if (!(runbits & ~collapsebit))
		return exithom ("Exiting after having collapsed "
			"the simplices. Thank you.");

	// ----- create a chain complex from the simplicial complex ------

	// create a chain complex from X (this is a relative chain complex!)
	chaincomplex<integer> cx (Xcompl. dim (), !!genname);
//	Xcompl. remove (Acompl);
	sout << "Creating the chain complex of X... ";
	createchaincomplex (cx, Xcompl);
	sout << "Done.\n";
	savetheset (cx, savefiles, "x.chn", Aname ?
		"the chain complex of (X,A)" : "the chain complex of X");

	// if no more things have to be done, exit now
	if (!(runbits & ~(collapsebit | chainbit)))
		return exithom ("Exiting after having created "
			"the chain complexes. Thank you.");

	// show how much time was used for the reduction
	program_time. show ("Time used so far:");

	// ----- compute and show homology, save generators -----

	// compute the homology of the chain complex of X
	chain<integer> *hom_cx;
	sout << "Computing the homology of X over " <<
		integer::ringname () << "...\n";
	cx. compute_and_show_homology (sout, hom_cx, level);

	// save the Betti numbers for X if requested to
	savebetti (bettiname, hom_cx, Xdim, Xorigdim);

	// save the generators of X to a file
	savegenerators (genname, "X", hom_cx, cx, Xcompl, level);

	program_time. show ("Total time used:");
	program_time = 0;
	scon << "[Press Ctrl-C to exit.]\r";
	return 0;
} /* homcubes */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// turn on a message that will appear if the program does not finish
	program_time = "Aborted after";

	// prepare user-configurable data
	char *Xname = NULL, *Aname = NULL;
	char *keepname = NULL, *genname = NULL, *bettiname = NULL;
	char *savefiles = NULL;
	short int runonly [8] = {0, 0, 0, 0, 0, 0, 0, 0};
	int runcount = 0;
	int levellist [Simplex::MaxDim + 1], level [Simplex::MaxDim + 1];
	int levelcount = 0;
	for (int i = 0; i < Simplex::MaxDim; i ++)
		level [i] = 0;
	int p = 0;
	bool dontcollapse = false;
	bool dontaddfaces = false;

	// analyze the command line
	arguments a;
	arg (a, NULL, Xname);
	arg (a, NULL, Aname);
	arg (a, "k", keepname);
	arg (a, "g", genname);
	arg (a, "b", bettiname);
	arg (a, "l", levellist, levelcount, Simplex::MaxDim + 1);
	arg (a, "s", savefiles, "");
	arg (a, "p", p);
	arg (a, "r", runonly, runcount, 8);
	argswitch (a, "d", dontaddfaces, true);
	argswitch (a, "C", dontcollapse, true);
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's title
	if (argresult >= 0)
		sout << title << '\n';

	// adjust the run-only bits
	int runbits = runcount ? 0 : ~0;
	for (int i = 0; i < runcount; i ++)
		if (runonly [i] > 0)
			runbits |= (0x01 << (runonly [i] - 1));

	// transform a list of levels to level bits
	for (int i = 0; i < Simplex::MaxDim + 1; i ++)
		level [i] = levelcount ? 0 : 1;
	for (int i = 0; i < levelcount; i ++)
	{
		if ((levellist [i] >= 0) &&
			(levellist [i] <= Simplex::MaxDim))
		{
			level [levellist [i]] = 1;
		}
		else
		{
			sout << "Requested homology level " <<
				levellist [i] << " is out of range.\n";
			argresult = -1;
			break;
		}
	}

	// adjust the ring of integers modulo p if requested for
	if (p > 0)
		integer::initialize (p);

	// show some debug info
	if (argresult >= 0)
		sout << "[Tech info: simpl " << sizeof (simplex) <<
			", chain " << sizeof (chain<integer>) <<
			", addr " << sizeof (int *) <<
			", intgr " << sizeof (integer) << ".]\n";

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if ((argresult > 0) || !Xname)
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	int result = 0;
	try
	{
		homsimpl (Xname, Aname, keepname, savefiles, genname,
			bettiname, level, dontaddfaces, dontcollapse,
			runbits);
		scon << "Thank you for using this software. "
			"We appreciate your business.\n";
	}
	catch (const char *msg)
	{
		sout << "ERROR: " << msg << '\n';
		result = -1;
	}
	catch (const std::exception &e)
	{
		sout << "ERROR: " << e. what () << '\n';
		result = -1;
	}
	catch (...)
	{
		sout << "ABORT: An unknown error occurred.\n";
		result = -1;
	}

	return result;
} /* main */

/// @}

