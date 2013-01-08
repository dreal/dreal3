/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file homcubes.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in December 1997. Last revision: May 2, 2008.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
#include "capd/homology/homtools.h"

#include <cstdlib>
#include <ctime>
#include <new>
#include <iostream>
#include <fstream>
#include <iomanip>

using namespace capd::homology;


// --------------------------------------------------
// -------------------- OVERTURE --------------------
// --------------------------------------------------

#ifdef SIMPLIFIED
const char *title = "\
CHomP, ver. 3.07, 07/21/10. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";
#else
const char *title = "\
HOMCUBES, ver. 3.07, 07/21/10. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";
#endif

#ifdef SIMPLIFIED
const char *helpinfo = "\
This program computes Betti numbers of a cubical set and writes them to\n\
the standard output (separated with spaces). No other output is written,\n\
except the error message if an error is encountered.\n\
Call this program with an input file name. Optional arguments:\n\
-b filename - save Betti numbers to a file (one number per line).\n\
-w n - wrap the space (repeat for each axis, use 0 for no space wrapping),\n\
--help - display this brief help information.\n\
For more information consult the Computational Homology Project website\n\
or ask the program's author directly at http://www.PawelPilarczyk.com/.";
#else
const char *helpinfo = "\
This program computes relative homology of cubical sets and cubical\n\
multivalued maps with the extensive use of geometrical reduction.\n\
Call with:\n\
X.cub [A.cub] / X.cel [A.cel] - for homology computation of X or (X+A, A),\n\
F.map [[X.cub] Y.cub] - for homology computation of a map F: X -> Y,\n\
F.map [X.cub] A.cub Y.cub B.cub - for F: (X+A, A) -> (Y+B, B),\n\
F.map -i [[X.cub] A.cub] - for F: X -> X or F: (X+A, A) -> (X+A, A).\n\
Switches and additional arguments:\n\
-k file - keep these cubes/cells in X (while reducing); repeat for Y,\n\
-g file - save homology generators of X (repeat for Y and map's graph F),\n\
-gf n - format of generators saved: 0 = text (default), 1 = chl format,\n\
-c file - read through this file first to fix the right numbers of cubes,\n\
-s prefix - save intermediate data; add the given prefix to file names,\n\
-l n - compute only this homology level,\n\
-b file - save Betti numbers to the given file,\n\
-m n - use at most n megabytes of memory for bit fields while reducing,\n\
-w n - wrap the space (repeat for each axis, use 0 for no space wrapping),\n\
-p n - perform the computations in the field of integers modulo prime n,\n\
-r n - run only these stages: 1: reduce full-dim cubes, 2: expand A in X,\n\
       3: expand A in X with F, 4: reduce the cells in (X,A),\n\
       5: create the graph of F, 6: reduce cells (Y,B),\n\
       7: create chain complexes, 8: compute homology.\n\
-d - don't add faces to cells (assume missing cells belong in A or B),\n\
-a - ensure that map's acyclicity is preserved during reduction (slow),\n\
-i - compute the map as an index map (X is contained in Y, A in B),\n\
-t3 file - read/write tabulated 3d neighborhoods from/to file,\n\
-h - display this brief help information only and exit.\n"
// MSVC++ 6.0 says that the string is too long(!) This is why it is split...
"Other switches (for debug and tests; may be removed or changed soon):\n\
-R - don't reduce fulldim, -G - use full graph, -C - don't collapse faces,\n\
-E - don't expand at all, -EF - don't expand (X,A) only if map is used,\n\
-V - don't verify the assumptions on the cubical map (must use chkmvmap),\n\
-O - old-style map output, -A - don't check acyclicity of the map,\n\
-T - do not use tabulated neighborhood configurations (dim 1-3 only);\n\
-B - don't use BDDs (dim 1-3 only), -M - use Malandain's code (dim3);\n\
--seq file - save the sequences of added/erased cells to the given file;\n\
--rand n - use the random numbers generator n times to change reductions;\n\
--hack n - some hacks for testing purposes only (don't use this!)\n\
For more information consult the accompanying documentation (if available)\n\
or ask the program's author at http://www.PawelPilarczyk.com/.";
#endif



// --------------------------------------------------
// --------------------- WRITE ----------------------
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
		int_t count = 0;
		for (int_t j = 0; j < hom [i]. size (); j ++)
			if (hom [i]. coef (j). delta () == 1)
				count ++;
		out << count << '\n';
	}
	for (int j = dim + 1; j < spacedim; j ++)
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
	const cubicalcomplex &Xcompl, int *level, int Xspacedim,
	int genformat)
{
	if (!filename)
		return;
	sout << "Saving generators of " << name << " to '" << filename <<
		"'... ";
	std::ofstream out (filename);
	if (!out)
		fileerror (filename, "create");
	writegenerators (out, hom_cx, cx, Xcompl, level, Xspacedim,
		genformat);
	sout << "Done.\n";
	return;
} /* savegenerators */

static void savetwocubes (const cubes &c1, const cubes &c2,
	const char *filename, const char *name)
// Write the union of the given two sets of cubes to a file with given name.
// Display a warning if unsuccessful.
// *** FOR BACKWARDS COMPATIBILITY ONLY
{
	// if no file name is given, do nothing
	if (!filename)
		return;

	// create the output file
	std::ofstream out (filename);
	if (!out)
	{
		sout << "WARNING: Cannot save cubes to '" << filename <<
			"'.\n";
		return;
	}

	// write the cubes to the output file
	sout << "Saving the cubes in " << name << " to '" << filename <<
		"'... ";
	out << "; This is " << name;
	if (c2. size ())
		out << " (" << (c1. size () + c2. size ()) <<
			" cubes total).\n";
	else
		out << ".\n";
	out << c1;
	if (c2. size ())
		out << "; ------------------\n" << c2;
	sout << "Done.\n";
	return;
} /* savetwocubes */


// --------------------------------------------------
// -------------------- HOMCUBES --------------------
// --------------------------------------------------

enum runbitnames
{
	fulldimbit = 0x01, expandAbit = 0x02, expandFbit = 0x04,
	cellsXbit = 0x08, graphFbit = 0x10, expandYbit = 0x20,
	chainbit = 0x40, hombit = 0x80
};

static int homcubes (const char *mapname,
	const char *Xcubname, const char *Acubname,
	const char *Ycubname, const char *Bcubname,
	const char *Xcelname, const char *Acelname,
	const char *Ycelname, const char *Bcelname,
	const char *Xkeepcubname, const char *Ykeepcubname,
	const char *Xkeepcelname, const char *Ykeepcelname,
	const char *savefiles,
	const char *Xfinalname, const char *Yfinalname,
	const char *Xgenname, const char *Ygenname, const char *Fgenname,
	int genformat, const char *bettiname, const char *cubelist,
	int *level, bool indexmap,
	int checkacyclic, bool dontaddfaces, bool fullgraph,
	bool dontcollapse, int runbits, bool verify, bool oldoutput, int hack)
{
	// read through the list of cubes to establish the right cube numbers
	scancubes<Cube> (cubelist);

	// determine the minimal homology level of interest
	int minlevel = 0;
	while (level && !level [minlevel] && (minlevel < Cube::MaxDim))
		minlevel ++;

	// ----- read the sets of cubes -----

	// read the set of cubes X
	cubes Xcubes;
	readelements (Xcubname, Xcubes, "X");

	// if X should be extracted from the map file, read it this way
	if (mapname && !Xcubname && !Xcelname)
	{
		readmapdomain (mapname, Xcubes);
		// make the impression that X was read from a file with cubes
		Xcubname = mapname;
	}

	// read the set of cubes A
	cubes Acubes;
	readelements (Acubname, Acubes, "A");

	// remove from X cubes which are in A
	removeAfromX (Xcubes, Acubes, "X", "A");

	// write the sets to the sequential output data
	if (sseq. show || sseq. log)
	{
		sseq << "\"Reading the initial pair (X,A)...\"\n";
		sseq << "D 0\n";
		if (mapname)
			sseq << "L\n";
		for (int_t i = 0; i < Xcubes. size (); ++ i)
			sseq << '1' << Xcubes [i] << '\n';
		for (int_t j = 0; j < Acubes. size (); ++ j)
			sseq << '2' << Acubes [j] << '\n';
		sseq << "D 100\n";
	}

	// if the set X is empty, the answer is obvious
	if (Xcubname && !Xcubes. size ())
	{
		if (Acubname)
			return exithom ("The set X is contained in A. "
				"The relative homology of (X,A) is trivial.",
				bettiname);
		else
			return exithom ("The set X is empty. "
				"The homology of X is trivial.", bettiname);
	}

	// leave in A only the neighbors of X\\A
	if (Acubes. size ())
		sseq << "P \"Restricting A to the neighbors of X...\"\n";
	restrictAtoneighbors (Xcubes, Acubes, "X", "A");

	// remember the original size of the set A and of the set X
	int_t origAsize = Acubes. size ();
	int_t origXsize = Xcubes. size ();

	// read cubes to keep in X
	cubes Xkeepcubes;
	readelements (Xkeepcubname, Xkeepcubes, "Xkeep");

	// read the set of cubes Y
	cubes Ycubes;
	readelements (Ycubname, Ycubes, "Y");

	// if Y should be the same as X, copy it
	if (mapname && indexmap && Xcubname && !Ycubname)
	{
		Ycubes = Xcubes;
		// make the impression that Y was read from a file with cubes
		Ycubname = Xcubname;
	}

	// if Y should be extracted from the map file, read it this way
	if (mapname && !indexmap && Xcubname && !Ycubname)
	{
		readmapimage (mapname, Ycubes);
		// make the impression that Y was read from a file with cubes
		Ycubname = mapname;
	}

	// read the set of cubes B
	cubes Bcubes;
	readelements (Bcubname, Bcubes, "B");

	// copy B from A if necessary
	if (mapname && indexmap && Acubname && !Bcubname &&
		(Ycubname == Xcubname))
	{
		Bcubes = Acubes;
		// make the impression that B was read from a file with cubes
		Bcubname = Acubname;
	}

	// remove from Y cubes which are in B
	removeAfromX (Ycubes, Bcubes, "Y", "B");

	// write the sets to the sequential output data
	if (sseq. show || sseq. log)
	{
		if (mapname)
			sseq << "R\n";
		sseq << "D 0\n";
		if (Ycubes. size () || Bcubes. size ())
			sseq << "P \"Reading the initial pair (Y,B)...\"\n";
		for (int_t i = 0; i < Ycubes. size (); i ++)
			sseq << '1' << Ycubes [i] << '\n';
		for (int_t j = 0; j < Bcubes. size (); j ++)
			sseq << '2' << Bcubes [j] << '\n';
		sseq << "D 100\n";
	}

	// if there are no cubes left in Y, then the map is trivial
	if (mapname && Ycubname && !Ycubes. size ())
	{
		if (Bcubname)
		{
			return exithom ("Y is a subset of B. "
				"The homology of (Y,B) is trivial "
				"and the map is zero.\n");
		}
		else
		{
			return exithom ("Y is empty. The homology "
				"of Y is trivial and the map is zero.\n");
		}
	}

	// determine the dimension of X and Y if possible
	int Xspacedim = (Xcubes. size ()) ? Xcubes [0]. dim () : -1;
	int Yspacedim = (Ycubes. size ()) ? Ycubes [0]. dim () : -1;

	// verify if X\A \subset Y and A \subset B in the index map case
	if (verify && indexmap && (Ycubname != Xcubname))
		checkinclusion (Xcubes, Ycubes, Bcubes, "X\\A", "Y");
	if (verify && indexmap && Acubes. size () && (Acubname != Bcubname))
		checkinclusion (Acubes, Bcubes, "A", "B");

	// ----- reduce the sets of cubes -----

	// allocate a suitable bit field set for the reduction and show msg
	if (runbits & fulldimbit & (Xspacedim > 0))
		knownbits [Xspacedim];

	// reduce the pair of sets of cubes (X,A) without acyclicity check
	if (mapname)
		sseq << "L\n";
	if ((runbits & fulldimbit) && !Xcubes. empty () && (checkacyclic < 2))
	{
		// expand A within X if necessary and restrict A to neighbors
		if ((runbits & expandAbit) && !mapname && !Acubes. empty ())
		{
			sseq << "P \"Expanding A within X...\"\n";
			expandAinX (Xcubes, Acubes, "X", "A");
			sseq << "P \"Restricting A to the neighbors "
				"of X...\"\n";
			restrictAtoneighbors (Xcubes, Acubes, "X", "A");
		}

		// reduce the pair (X,A)
		if (!Acubes. empty ())
			sseq << "P \"Reducing the pair (X,A)...\"\n";
		else
			sseq << "P \"Reducing the cubes from X...\"\n";
		reducepair (Xcubes, Acubes, Xkeepcubes, "X", "A");

		// if nothing remains in X, then the result is trivial
		if (Xcubes. empty ())
			return exithom ("There are no cubes left "
				"in X\\A. The homology of (X,A) "
				"is trivial.", bettiname);
	}

	// remember which inclusions have been verified
	bool inclFABchecked = false;
	bool inclFXYchecked = false;

	// read the map on X or only on X\A for careful or extended reduction
	cubicalmap FcubmapT;
	if (mapname && (runbits & fulldimbit) && (checkacyclic > 1))
	{
		readmaprestriction (FcubmapT, mapname, Xcubes, Acubes, "X",
			"for careful reduction");
		// check if F (X\A) \subset Y
		if (verify)
		{
			checkimagecontained (FcubmapT, Xcubes, Ycubes,
				Bcubes, Acubes. size () ? "X\\A" : "X", "Y");
			inclFXYchecked = true;
		}
		// check if F (A) \subset B and if F (A) is disjoint from Y
		if (verify && !Acubes. empty ())
		{
			checkimagecontained (FcubmapT, Acubes, Bcubes,
				"A", "B");
			checkimagedisjoint (FcubmapT, Acubes, Ycubes,
				"A", "Y\\B");
			inclFABchecked = true;
		}
	}
	else if ((runbits & fulldimbit) && (runbits & expandFbit) &&
		mapname && !Acubes. empty ())
	{
		readmaprestriction (FcubmapT, mapname, Xcubes,
			Acubes. size () ? "X\\A" : "X",
			"for extended reduction");
		// check if F (X\A) \subset Y
		if (verify)
		{
			checkimagecontained (FcubmapT, Xcubes, Ycubes,
				Bcubes, Acubes. size () ? "X\\A" : "X", "Y");
			inclFXYchecked = true;
		}
	}

	// expand A within X and modify (Y,B) if requested to
	if ((runbits & fulldimbit) && (runbits & expandFbit) &&
		mapname && Acubes. size ())
	{
		// expand A towards X and modify (Y,B) accordingly
		sseq << "P \"Expanding (X,A) with the map in mind...\"\n";
		sseq << "D 5\n";
		expandAinX (Xcubes, Acubes, Ycubes, Bcubes, FcubmapT,
			"X", "A", "B", indexmap, checkacyclic > 1);
		sseq << "D 100\n";
	}

	// reduce the pair (X,A) or the set X with acyclicity check
	if ((runbits & fulldimbit) && mapname && (checkacyclic > 1))
	{
		// leave in A only the neighbors of X\\A
		sseq << "L\n";
		sseq << "P \"Restricting A to the neighbors of X...\"\n";
		restrictAtoneighbors (Xcubes, Acubes, "X", "A");

		// reduce the pair (X,A) with acyclicity check
		if (!Acubes. empty ())
			sseq << "P \"Reducing the pair (X,A)...\"\n";
		else
			sseq << "P \"Reducing the cubes from X...\"\n";
		reducepair (Xcubes, Acubes, FcubmapT, Xkeepcubes, "X", "A");

		// if nothing remains in X, then the result is trivial
		if (Xcubes. empty ())
			return exithom ("There are no cubes left "
				"in X\\A. The homology of (X,A) "
				"is trivial.", bettiname);
	}

	// release the memory used by the map as no longer necessary
	cubicalmap empty;
	FcubmapT = empty;

	// reduce the pair (X,A) even further
	if ((runbits & fulldimbit) && mapname && (checkacyclic < 2) &&
		!Acubes. empty ())
	{
		// leave in A only the neighbors of X\\A
		sseq << "L\n";
		sseq << "P \"Restricting A to the neighbors of X...\"\n";
		restrictAtoneighbors (Xcubes, Acubes, "X", "A");

		// continue the reduction of the pair (X,A)
		sseq << "P \"Continuing with the reduction of (X,A)...\"\n";
		reducepair (Xcubes, Acubes, Xkeepcubes, "X", "A");
	}

	// save the cubes left after the reduction - an old version
	savetwocubes (Xcubes, Acubes, Xfinalname, "X after reduction");

	// save the cubes left in X and A after the reduction
	if (Xcubname)
		savetheset (Xcubes, savefiles, "x.cub",
			Acubname ? "the cubes in X\\A after reduction" :
			"the cubes in X after reduction");
	if (Acubname)
		savetheset (Acubes, savefiles, "a.cub",
			"the cubes in A after reduction");

	// indicate that the acyclicity of the map should be verified
	if (mapname && (checkacyclic >= 0))
	{
		if ((checkacyclic < 1) && ((origAsize != Acubes. size ()) ||
			(origXsize != Xcubes. size ())))
			sout << "*** Important note: X or A changed. "
				"You must make sure\n"
				"*** that the restriction of F "
				"to the new sets is acyclic.\n";
		else
		{
			if (checkacyclic < 1)
				sout << "*** ";
			sout << "Note: The program assumes "
				"that the input map is acyclic.\n";
		}
	}

	// add cubes from map's image to the set read from the file
	// to make sure that the map's image is a subset of its codomain
	if (mapname && Ycubname && (Ycubname != mapname) &&
		!Bcubname && !Bcelname)
		readmapimage (mapname, Ycubes);

	// read cubes to keep in Y
	cubes Ykeepcubes;
	readelements (Ykeepcubname, Ykeepcubes, "Ykeep");

	// read the map restricted to X\A
	cubicalmap Fcubmap;
	readmaprestriction (Fcubmap, mapname, Xcubes,
		Acubes. empty () ? "X" : "X\\A");

	// check if F (X\A) \subset Y
	if (mapname && verify && !inclFXYchecked)
	{
		checkimagecontained (Fcubmap, Xcubes, Ycubes, Bcubes,
			Acubes. empty () ? "X" : "X\\A", "Y");
		inclFXYchecked = true;
	}

	// read the map restricted to A
	cubicalmap FcubmapA;
	readmaprestriction (FcubmapA, mapname, Acubes, "A");

	// check if F (A) \subset B
	if (mapname && verify && !inclFABchecked && !Acubes. empty ())
	{
		checkimagecontained (FcubmapA, Acubes, Bcubes, "A", "B");
		checkimagedisjoint (FcubmapA, Acubes, Ycubes, "A", "Y\\B");
		inclFABchecked = true;
	}

	// add the image of the map of interest to the cubes to keep in Y
	addmapimg (Fcubmap, FcubmapA, Xcubes, Acubes, Ykeepcubes, indexmap);

	// reduce the pair of cubical sets (Y,B) towards the image of F
	if ((runbits & fulldimbit) && (Xspacedim == Yspacedim))
	{
		sseq << "R\n";
		if (runbits & expandAbit)
			expandAinX (Ycubes, Bcubes, "Y", "B");
		restrictAtoneighbors (Ycubes, Bcubes, "Y", "B", &Ykeepcubes);
		reducepair (Ycubes, Bcubes, Ykeepcubes, "Y", "B");
	}

	// save the cubes left after the reduction - an old version
	savetwocubes (Ycubes, Bcubes, Yfinalname, "Y after reduction");

	// save the cubes left in Y and B after the reduction
	if (Ycubname)
		savetheset (Ycubes, savefiles, "y.cub",
			Bcubname ? "the cubes in Y\\B after reduction" :
			"the cubes in Y after reduction");
	if (Bcubname)
		savetheset (Bcubes, savefiles, "b.cub",
			"the cubes in B after reduction");

	// show how many bit fields were in use and forget the bit fields now
	if (!mapname || (checkacyclic <= 0))
		knownbits. forget ();

	// if no more things have to be done, exit now
	if (!(runbits & ~(fulldimbit | expandAbit | expandFbit)))
		return exithom ("Exiting after having reduced "
			"full-dimensional cubes. Thank you.");

	// ----- read or create the cubical complexes -----

	// read the cubical complex of X
	cubicalcomplex Xcompl;
	readcells (Xcelname, Xcompl, "X");

	// transform the set of cubes X into a set of cells and forget Xcubes
	if (!Xcelname)
		cubes2cells (Xcubes, Xcompl, Acubes. empty () ? "X" : "X\\A");
	else if (!Xcubes. empty ())
	{
		cubes empty;
		Xcubes = empty;
	}

	// read the cubical complex A
	cubicalcomplex Acompl;
	readcells (Acelname, Acompl, "A");

	// transform the set of cubes A into a set of cubical cells
	if (!Acelname)
		cubes2cells (Acubes, Acompl, "A");
	else if (!Acubes. empty ())
	{
		cubes empty;
		Acubes = empty;
	}

	// remove from X cells which are in A if it was not done previously
	if (!mapname && (Acelname || Xcelname))
		removeAfromX (Xcompl, Acompl, "X", "A");

	if (mapname)
		sseq << "L\n";

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

	// read cells to keep in X
	cubicalcomplex Xkeepcompl;
	readcells (Xkeepcelname, Xkeepcompl, "Xkeep");

	// transform the cubes to keep in X into cells and forget the cubes
	if (!dontcollapse && !Xkeepcelname)
		cubes2cells (Xkeepcubes, Xkeepcompl, "Xkeep");
	else if (!Xkeepcubes. empty ())
	{
		cubes empty;
		Xkeepcubes = empty;
	}

	// read the cubical complex of Y
	cubicalcomplex Ycompl;
	readcells (Ycelname, Ycompl, "Y");

	// transform the cubes in Y into cubical cells and forget the cubes
	if (!Ycelname)
		cubes2cells (Ycubes, Ycompl, Bcubes. empty () ? "Y" : "Y\\B");
	else if (!Ycubes. empty ())
	{
		cubes empty;
		Ycubes = empty;
	}

	// if Y should be the same as X, copy it
	if (mapname && indexmap && Xcelname && !Ycubname && !Ycelname)
		Ycompl = Xcompl;

	// read the cubical complex B
	cubicalcomplex Bcompl;
	readcells (Bcelname, Bcompl, "B");

	// transform the cubes in B into cubical cells and forget the cubes
	if (!Bcelname)
		cubes2cells (Bcubes, Bcompl, "B");
	else if (!Bcubes. empty ())
	{
		cubes empty;
		Bcubes = empty;
	}

	// copy B from A if necessary
	if (mapname && indexmap && !Bcubname && !Bcelname &&
		!Ycubname && !Ycelname && !Acompl. empty ())
		Bcompl = Acompl;

	// read cells to keep in Y
	cubicalcomplex Ykeepcompl;
	readcells (Ykeepcelname, Ykeepcompl, "Ykeep");

	// transform the cubes to keep in Y into cells and forget the cubes
	if (mapname && !dontcollapse && Ykeepcubname && !Ykeepcelname)
		cubes2cells (Ykeepcubes, Ykeepcompl, "Ykeep");
	else if (!Ykeepcubes. empty ())
	{
		cubes empty;
		Ykeepcubes = empty;
	}

	if (mapname)
		sseq << "R\n";

	// determine the dimension of X and Y as cubical complexes
	int Xdim = Xcompl. dim ();
	if ((Xspacedim < 0) && (Xdim >= 0))
		Xspacedim = Xcompl [Xdim] [0]. spacedim ();
	int Ydim = Ycompl. dim ();
	if ((Yspacedim < 0) && (Ydim >= 0))
		Yspacedim = Ycompl [Ydim] [0]. spacedim ();

	// set high homology levels to be ignored
	for (int i = Xdim + 1; level && (i < Cube::MaxDim); i ++)
		if (i > Ydim)
			level [i] = 0;

	// if the requested homology level is too large, the answer is simple
	if (minlevel > Xdim)
		return exithom ("The dimension of the set is lower "
			"than the requested homology level.");

	// ----- collapse the cubical sets (X,A) -----

	if (mapname)
		sseq << "L\n";

	// create a full cubical complex (with all the faces) of X\A
	if (dontcollapse && (hack != 1))
	{
		// decrease the dimension of A to the dimension of X
		decreasedimension (Acompl, Xdim, "A");

		// add boundaries to cells in X and A
		if (!dontaddfaces)
			addboundaries (Xcompl, Acompl, minlevel, !!mapname,
				"X", "A");
	}

	// reduce the pair of sets (Xcompl, Acompl) while adding to them
	// boundaries of all the cells
	if (!dontcollapse && (hack != 1))
	{
		if (!Acompl. empty ())
			sseq << "P \"Collapsing cubical faces "
				"in (X,A)...\"\n";
		else
			sseq << "P \"Collapsing cubical faces in X...\"\n";

		collapse (Xcompl, Acompl, Xkeepcompl, "X", "A",
			!dontaddfaces, mapname && !fullgraph,
			!mapname, level);

		// if nothing remains in X, then the result is trivial
		if (Xcompl. empty ())
			return exithom ("Nothing remains in X. "
				"The homology of (X,A) is trivial.\n",
				bettiname);
	}

	// forget the cells to keep in X
	if (!Xkeepcompl. empty ())
	{
		cubicalcomplex empty;
		Xkeepcompl = empty;
	}

	// make a correction to the dimension of X
	if (Xdim != Xcompl. dim ())
	{
		sout << "Note: The dimension of X decreased from " <<
			Xdim << " to " << Xcompl. dim () << ".\n";

		Xdim = Xcompl. dim ();
		for (int i = Xdim + 1; level && (i < Cube::MaxDim); i ++)
			if (i > Ydim)
				level [i] = 0;
	}

	// save the cells left in X and A after the reduction
	if (Xcubname || Xcelname)
		savetheset (Xcompl, savefiles, "x.cel",
			(Acubname || Acelname) ?
			"the cells in X\\A after reduction" :
			"the cells in X after reduction");
	if (Acubname || Acelname)
		savetheset (Acompl, savefiles, "a.cel",
			"the cells in A after reduction");

	// if no more things have to be done, exit now
	if (!(runbits & ~(fulldimbit | expandAbit | expandFbit | cellsXbit)))
		return exithom ("Exiting after having reduced "
			"the cubical sets. Thank you.");

	// ----- create a reduced graph of F -----

	// create the map F defined on the cells in its domain
	mvcellmap<qcell,integer,cube> Fcellcubmap (Xcompl);
	if (mapname && (hack != 1))
	{
		sout << "Creating the map F on cells in X... ";
		int_t count = createimages (Fcellcubmap, Fcubmap, FcubmapA);
		sout << count << " cubes added.\n";
	}

	// create the map F defined on the cells in its domain subcomplex A
	mvcellmap<qcell,integer,cube> FcellcubmapA (Acompl);
	if (mapname && !Acompl. empty () && (hack != 1))
	{
		sout << "Creating the map F on cells in A... ";
		int_t count = createimages (FcellcubmapA, FcubmapA);
		sout << count << " cubes added.\n";
	}

	// show how many bit fields were in use and forget the bit fields now
	knownbits. forget ();

	// create the full graph of F on A if requested
	cubicalcomplex FcomplA;
	if (mapname && fullgraph && !Acompl. empty ())
	{
		sout << "Creating the full graph of F|A... ";
		int_t prevA = FcomplA. size ();
		creategraph (FcellcubmapA, FcomplA, dontcollapse);
		sout << (FcomplA. size () - prevA) << " cells added.\n";
	}

	// create the full graph of F on X if requested
	cubicalcomplex Fcompl;
	if (mapname && fullgraph)
	{
		sout << "Creating the full graph of F... ";
		int_t prev = Fcompl. size ();
		creategraph (Fcellcubmap, FcomplA, Fcompl, dontcollapse);
		sout << (Fcompl. size () - prev) << " cells added.\n";

		// forget 'FcomplA' if it is not going to be used anymore
		if (dontcollapse && !FcomplA. empty ())
		{
			cubicalcomplex empty;
			FcomplA = empty;
		}
	}

	// create the graph of F as a cubical cell complex
	if (mapname && !fullgraph && (hack != 1))
	{
		sout << "Creating a cell map for F... ";
		mvcellmap<qcell,integer,qcell> Fcellmap (Xcompl);
		bool acyclic = createcellmap (Fcellcubmap, FcellcubmapA,
			Fcellmap, checkacyclic > 0);
		sout << "Done.\n";
		if ((checkacyclic > 0) && !acyclic)
			sout << "*** SERIOUS PROBLEM: The map is not "
				"acyclic. THE RESULT WILL BE WRONG.\n"
				"*** You must verify the acyclicity of the "
				"initial map with 'chkmvmap'\n"
				"*** and, if successful, run this program "
				"with the '-a' switch.\n";
		if ((checkacyclic > 0) && acyclic)
			sout << "Note: It has been verified successfully "
				"that the map is acyclic.\n";

		// save the reduced cell map for F if requested to
		if (mapname)
			savetheset (Fcellmap, savefiles, "f.clm",
				"the reduced cell map for F");

		sout << "Creating the graph of F... ";
		int_t prev = Fcompl. size ();
		creategraph (Fcellmap, Fcompl, false);
		sout << (Fcompl. size () - prev) << " cells added.\n";
	}

	// reduce the graph of F by free face collapses
	if (mapname && !dontcollapse && fullgraph)
	{
		int olddim = Fcompl. dim ();
		sout << "Collapsing the graph of F... ";
		cubicalcomplex empty;
		int_t count = Fcompl. collapse (FcomplA, empty, !dontaddfaces,
			false, true /*debug false*/, level);
		sout << 2 * count << " removed, " << Fcompl. size () <<
			" left.\n";
		if (Fcompl. dim () != olddim)
			sout << "Note: The dimension of the graph "
				"decreased from " << olddim << " to " <<
				Fcompl. dim () << ".\n";
		// forget the graph on A as no longer necessary
		if (!FcomplA. empty ())
		{
			sout << "The graph of F on A discarded.\n";
			cubicalcomplex empty;
			FcomplA = empty;
		}
	}

	// save the created graph of F if requested to
	if (mapname)
		savetheset (Fcompl, savefiles, "f.cel",
			"the reduced graph of F");

	// if no more things have to be done, exit now
	if (!(runbits & ~(fulldimbit | expandAbit | expandFbit | cellsXbit |
		graphFbit)))
		return exithom ("Exiting after having reduced "
			"the graph of F. Thank you.");

	// forget the cubical map on the cells
	if (mapname)
	{
		mvcellmap<qcell,integer,cube> empty;
		Fcellcubmap = empty;
		FcellcubmapA = empty;
	}

	// ----- collapse the cubical sets (Y,B) -----

	if (mapname)
		sseq << "R\n";

	// hack: read the map's graph from "f.cel" at this point
	if (hack == 1)
	{
		cubicalcomplex empty;
		Fcompl = empty;
		readcells ("f.cel", Fcompl, "the graph of F (HACK!)");
	}

	// decrease the dimension of B to the dimension of Y
	decreasedimension (Bcompl, Ydim, "B");

	// create a full cubical complex (with all the faces) of Y\B
	if (!Ycompl. empty ())
	{
		if (!dontaddfaces)
			addboundaries (Ycompl, Bcompl, minlevel, false,
				"Y", "B");

		// forget the cubical complex of B
		if (!Bcompl. empty ())
		{
			sout << "Forgetting " << Bcompl. size () <<
				" cells from B.\n";
			cubicalcomplex empty;
			Bcompl = empty;
		}
	}

	// collapse the codomain of the map towards the image of F
	if (mapname && !dontcollapse)
	{
		sout << "Computing the image of F... ";
		if (hack == 1)
		{
			cubicalcomplex empty;
			Ykeepcompl = empty;
			sout << "Debug: X space dim = " << Xspacedim <<
				", Y space dim = " << Yspacedim << ".\n";
		}
		int_t prev = Ykeepcompl. size ();
		project (Fcompl, Ykeepcompl, Ycompl, Xspacedim, Yspacedim,
			0, level, false);
		if (indexmap)
			project (Fcompl, Ykeepcompl, Ycompl, 0, Xspacedim,
				Yspacedim, level, false);
		sout << (Ykeepcompl. size () - prev) << " cells added.\n";

		// for debug purposes only (hack?)
	//	savetheset (Ykeepcompl, savefiles, "f_img.cel",
	//		"the image of F (and i)");
	//	savetheset (Ycompl, savefiles, "y_nonred.cel",
	//		"the cells in Y before the reduction");

		sout << "Collapsing Y towards F(X)... ";
		cubicalcomplex empty;
		int_t count = Ycompl. collapse (empty, Ykeepcompl,
			0, 0, 0, level);
		sout << 2 * count << " cells removed, " << Ycompl. size () <<
			" left.\n";
	}

	// forget the cells to keep in Y
	if (!Ykeepcompl. empty ())
	{
		cubicalcomplex empty;
		Ykeepcompl = empty;
	}

	// save the cells left in Y and B after the reduction
	if (Ycubname || Ycelname)
		savetheset (Ycompl, savefiles, "y.cel",
			(Bcubname || Bcelname) ?
			"the cells in Y\\B after reduction" :
			"the cells in Y after reduction");
	if (Bcubname || Bcelname)
		savetheset (Bcompl, savefiles, "b.cel",
			"the cells in B after reduction");

	// make a correction to the dimension of Y
	if (Ydim != Ycompl. dim ())
	{
		sout << "Note: The dimension of Y decreased from " <<
			Ydim << " to " << Ycompl. dim () << ".\n";

		Ydim = Ycompl. dim ();
		for (int i = Ydim + 1; level && (i < Cube::MaxDim); i ++)
			if (i > Xdim)
				level [i] = 0;
	}

	// if no more things have to be done, exit now
	if (!(runbits & ~(fulldimbit | expandAbit | expandFbit | cellsXbit |
		graphFbit | expandYbit)))
		return exithom ("Exiting after having reduced "
			"all the cubical sets. Thank you.");

	// ----- create chain complexes from the cubical sets ------

	// create a chain complex from X (this is a relative chain complex!)
	chaincomplex<integer> cx (Xcompl. dim (), !!Xgenname);
	if (!mapname)
	{
	//	Xcompl. remove (Acompl);
		sout << "Creating the chain complex of X... ";
		createchaincomplex (cx, Xcompl);
		sout << "Done.\n";
		savetheset (cx, savefiles, "x.chn", (Acubname || Acelname) ?
			"the chain complex of (X,A)" :
			"the chain complex of X");
	}

	// create a chain complex from the graph of F (it is relative)
	chaincomplex<integer> cgraph (Fcompl. dim (), !!Xgenname);
	if (mapname)
	{
		sout << "Creating the chain complex of the graph of F... ";
		createchaincomplex (cgraph, Fcompl);
		sout << "Done.\n";
		savetheset (cgraph, savefiles, "f.chn",
			"the chain complex of the graph of F");
	}

	// create the chain complex from Y (this is a relative complex)
	chaincomplex<integer> cy (Ydim, !!Ygenname);
	if (mapname)
	{
		sout << "Creating the chain complex of Y... ";
		createchaincomplex (cy, Ycompl);
		sout << "Done.\n";
		savetheset (cy, savefiles, "y.chn", (Bcubname || Bcelname) ?
			"the chain complex of (Y,B)" :
			"the chain complex of Y");
	}

	// create the projection map from the graph of the map to Y
	chainmap<integer> cmap (cgraph, cy);
	if (mapname)
	{
		sout << "Creating the chain map of the projection... ";
		createprojection (Fcompl, Ycompl, cmap, Xspacedim,
			Yspacedim, 0, level);
		sout << "Done.\n";
		savetheset (cmap, savefiles, "f.chm", "the chain map of F");
	}

	// if this is an index map, create the projection map from the graph
	// of the map to X composed with the inclusion into Y
	chainmap<integer> imap (cgraph, cy);
	if (mapname && indexmap)
	{
		sout << "Creating the chain map of the inclusion... ";
		createprojection (Fcompl, Ycompl, imap, 0, Xspacedim,
			Yspacedim, level);
		sout << "Done.\n";
		savetheset (imap, savefiles, "i.chm",
			"the chain map of the inclusion");
	}

	// forget the graph of F if it is not going to be used anymore
	if (!Fcompl. empty () && !Xgenname && !Fgenname)
	{
		cubicalcomplex empty;
		Fcompl = empty;
	}

	// forget the coordinates of cubes if they are not needed anymore
	if (!Xgenname && !Ygenname && !Fgenname)
	{
		PointBase::showused (sout);
		PointBase::forget ();
	}

	// if no more things have to be done, exit now
	if (!(runbits & ~(fulldimbit | expandAbit | expandFbit | cellsXbit |
		graphFbit | expandYbit | chainbit)))
		return exithom ("Exiting after having created "
			"the chain complexes. Thank you.");

	// show how much time was used for the reduction
	program_time. show ("Time used so far:");

	// ----- compute and show homology, save generators -----

	// compute the homology of the chain complex of X
	chain<integer> *hom_cx = 0;
	if (!mapname)
	{
		sout << "Computing the homology of X over " <<
			integer::ringname () << "...\n";
		cx. compute_and_show_homology (sout, hom_cx, level);
	}

	// compute the homology of the chain complex of the graph of the map
	chain<integer> *hom_cgraph = 0;
	if (mapname)
	{
		sout << "Computing the homology of the graph of F over " <<
			integer::ringname () << "...\n";
		cgraph. compute_and_show_homology (sout, hom_cgraph, level);
	}

	// save the Betti numbers for X if requested to
	savebetti (bettiname, mapname ? hom_cgraph : hom_cx,
		Xdim, Xspacedim);

	#ifdef SIMPLIFIED
	// show the Betti numbers for X in the simplified version
	{
		const chain<integer> *hom = mapname ? hom_cgraph : hom_cx;
		sout. show = true;
		for (int i = 0; i <= Xdim; i ++)
		{
			int_t count = 0;
			for (int_t j = 0; j < hom [i]. size (); j ++)
				if (hom [i]. coef (j). delta () == 1)
					count ++;
			if (i)
				sout << ' ';
			sout << count;
		}
		for (int j = Xdim + 1; j < Xspacedim; j ++)
		{
			if (j)
				sout << ' ';
			sout << '0';
		}
		sout << '\n';
		sout. show = false;
	}
	#endif

	// save the generators of X to a file
	if (mapname)
		savegenerators (Xgenname, "X", hom_cgraph, cgraph, Fcompl,
			level, Xspacedim, genformat);
	else
		savegenerators (Xgenname, "X", hom_cx, cx, Xcompl,
			level, Xspacedim, genformat);

	// save the generators of the graph of the map to a file
	savegenerators (Fgenname, "the graph of F", hom_cgraph, cgraph,
		Fcompl, level, Xspacedim + Yspacedim, genformat);

	// compute the homology of the chain complex of Y
	chain<integer> *hom_cy = 0;
	if (mapname)
	{
		sout << "Computing the homology of Y over " <<
			integer::ringname () << "...\n";
		cy. compute_and_show_homology (sout, hom_cy, level);
	}

	// save the generators of Y to a file
	savegenerators (Ygenname, "Y", hom_cy, cy, Ycompl, level, Yspacedim,
		genformat);

	// ----- show the map(s) -----

	// show the output in the old manner if requested to
	if (oldoutput)
	{
		// show the map induced in homology by the chain map
		if (mapname)
		{
			sout << "The map induced in homology "
				"is as follows:\n";
			cmap. show_homology (sout, hom_cgraph, hom_cy, level,
				"x", "y");
		}

		// show the map induced in homology by the inclusion map
		if (mapname && indexmap)
		{
			sout << "The map induced in homology "
				"by the inclusion:\n";
			imap. show_homology (sout, hom_cgraph, hom_cy, level,
				"x", "y");
		}
	}

	// determine the maximal non-trivial homology level for maps
	int homdimgraph = cgraph. dim ();
	while ((homdimgraph >= 0) && ((level && !level [homdimgraph]) ||
		(!hom_cgraph [homdimgraph]. size ())))
		homdimgraph --;
	int homdimy = cy. dim ();
	while ((homdimy >= 0) && ((level && !level [homdimy]) ||
		(!hom_cy [homdimy]. size ())))
		homdimy --;
//	if (mapname)
//		sout << "Maximal homology level considered for the map "
//			"is " << homdim << ".\n";

	// prepare the data structures for the homology
	chaincomplex<integer> hgraph (homdimgraph);
	chaincomplex<integer> hy (homdimy);
	chainmap<integer> hmap (hgraph, hy);
	chainmap<integer> hincl (hgraph, hy);
	chainmap<integer> hincldebug (hgraph, hy);
	chainmap<integer> hcomp (hgraph, hgraph);

	// show the map induced in homology by the chain map
	if (mapname)
	{
		sout << "The map induced in homology is as follows:\n";
		hgraph. take_homology (hom_cgraph);
		hy. take_homology (hom_cy);
		hmap. take_homology (cmap, hom_cgraph, hom_cy);
		hmap. show (sout, "\tf", "x", "y", level);
	}

	// show the map induced in homology by the inclusion map
	if (mapname && indexmap)
	{
		sout << "The map induced in homology by the inclusion:\n";
		hincl. take_homology (imap, hom_cgraph, hom_cy);
		hincldebug. take_homology (imap, hom_cgraph, hom_cy);
		hincl. show (sout, "\ti", "x", "y", level);

		bool invertible = true;
		try
		{
			hincl. invert ();
		}
		catch (...)
		{
			sout << "Oh, my goodness! This map is apparently "
				"not invertible.\n";
			invertible = false;
			throw "Unable to invert the inclusion map.";
		}

		if (invertible)
		{
			sout << "The inverse of the map "
				"induced by the inclusion:\n";
			hincl. show (sout, "\tI", "y", "x", level);

			// debug: verify if the map was inverted correctly
			chainmap<integer> hincl1 (hgraph, hy);
			hincl1. take_homology (imap, hom_cgraph, hom_cy);
			chainmap<integer> hident (hy, hy);
			hident. compose (hincl1, hincl);
			sbug << "The composition of the inclusion and "
				"its inverse (should be the identity):\n";
			hident. show (sbug, "\tid", "y", "y", level);
			for (int i = 0; i <= hident. dim (); ++ i)
			{
				const mmatrix<integer> &m = hident [i];
				if (m. getnrows () != m. getncols ())
					throw "INV: Inequal rows and cols.";
				integer zero, one;
				zero = 0;
				one = 1;
				for (int c = 0; c < m. getncols (); ++ c)
				{
					for (int r = 0; r < m. getnrows (); ++ r)
					{
						if ((r == c) && (m. get (r, c) == one))
							continue;
						if (m. get (r, c) == zero)
							continue;
						throw "INV: Non-identity.";
					}
				}
			}
			// debug: end of the verification

			sout << "The composition of F and the inverse "
				"of the map induced by the inclusion:\n";
			hcomp. compose (hincl, hmap);
			hcomp. show (sout, "\tF", "x", "x", level);
		}
	}

	program_time. show ("Total time used:");
	program_time = 0;
	scon << "[Press Ctrl-C to exit.]\r";
	return 0;
} /* homcubes */


// --------------------------------------------------
// --------------------- TOOLS ----------------------
// --------------------------------------------------

struct filetype
{
	enum name {unknown, wrong, setofcubes, setofcells,
		cubicalmap, almostperfectmap, empty};

}; /* struct filetype */

static filetype::name detectfiletype (const char *name)
{
	// open the input file
	std::ifstream in (name);
	if (!in)
		fileerror (name);
	ignorecomments (in);

	// if the file begins with "Space Dimension", then this is an
	// almost perfect map
	if ((in. peek () == 'S') || (in. peek () == 's'))
		return filetype::almostperfectmap;

	// if the file begins with "Type of set", then this is a
	// cubical set in the 'book' format
	if ((in. peek () == 'T') || (in. peek () == 't'))
		return filetype::setofcells;

	// ignore the word "dimension"
	if ((in. peek () == 'd') || (in. peek () == 'D'))
	{
		ignoreline (in);
		ignorecomments (in);
	}

	// if there is nothing to read, then this is an empty set
	if (in. peek () == EOF)
		return filetype::empty;

	// if there are two opening parentheses, then this is a set of cells

	int p1 = EOF;
	if ((in. peek () < '0') || (in. peek () > '9'))
		p1 = readparenthesis (in);
//	if (p1 == EOF)
//		return filetype::wrong;
	ignorecomments (in);
	int p2 = EOF;
	if (p1 != EOF)
		p2 = readparenthesis (in);
	if (p2 != EOF)
		return filetype::setofcells;

	// look for "->" to determine whether this is a cubical map
	// and look for "x" to see if this is a set of cells
	for (int count = 0; count < 500; count ++)
	{
		ignorecomments (in);
		int ch = in. get ();
		if ((ch == '-') && (in. peek () == '>'))
			return filetype::cubicalmap;
		else if ((ch == 'x') || (ch == 'X'))
			return filetype::setofcells;
	}

	// if "->" not found, the file apparently contains a set of cubes
	return filetype::setofcubes;
} /* detectfiletype */

static void insertname (char *tab [], char *name, int pos, int maxpos)
{
	for (int i = maxpos; i > pos; i --)
		tab [i] = tab [i - 1];
	tab [pos] = name;
	return;
} /* insertname */

static int splitfiles (char *filenames [], int namecount,
	char *cubnames [], int &ncub, char *celnames [], int &ncel,
	char **mapname = NULL, bool *almostperfect = NULL)
// Split files into tables according to the type of each file.
// The variables 'ncub' and 'ncel' contain the maximal number of entries
// allowed; their value is replaced with the actual number of entries found.
// Return 0 on success or -1 if the program should be interrupted.
{
	const int maxempty = 10;
	char *emptyfiles [maxempty];
	int emptyposcub [maxempty], emptyposcel [maxempty];
	int nempty = 0;

	int maxcub = ncub, maxcel = ncel;
	ncub = 0;
	ncel = 0;
	int i; // global variable for iterations - necessary for MSVC++
	for (i = 0; i < namecount; i ++)
	{
		// detect the type of the file
		filetype::name type /*= filetype::unknown*/;
		try
		{
			type = detectfiletype (filenames [i]);
		}
		catch (char *msg)
		{
			sout << "ERROR: " << msg << '\n';
			return -1;
		}

		// assign the file name to a suitable variable
		if (mapname && ((type == filetype::cubicalmap) ||
			(type == filetype::almostperfectmap)))
		{
			if (*mapname)
				sout << "WARNING: Too many files "
				"with maps; ignoring '" <<
				filenames [i] << "'.\n";
			else
			{
				if ((type == filetype::almostperfectmap) &&
					almostperfect)
					*almostperfect = true;
				*mapname = filenames [i];
			}
		}
		else if (type == filetype::setofcubes)
		{
			if (ncub < maxcub)
				cubnames [ncub ++] = filenames [i];
			else
				sout << "WARNING: Too many files "
					"with cubes; ignoring '" <<
					filenames [i] << "'.\n";
		}
		else if (type == filetype::setofcells)
		{
			if (ncel < maxcel)
				celnames [ncel ++] = filenames [i];
			else
				sout << "WARNING: Too many files "
					"with cells; ignoring '" <<
					filenames [i] << "'.\n";
		}
		else if (type == filetype::empty)
		{
			if (nempty < maxempty)
			{
				emptyfiles [nempty] = filenames [i];
				emptyposcub [nempty] = ncub;
				emptyposcel [nempty] = ncel;
				nempty ++;
			}
			else
				sout << "WARNING: Too many empty files: "
					"ignoring '" << filenames [i] <<
					"'.\n";
		}
		else
		{
			sout << "ERROR: The contents of '" <<
				filenames [i] << "' cannot be "
				"recognized.\n";
			return -1;
		}
	}

	int insertedcub = 0;
	int insertedcel = 0;
	for (i = 0; i < nempty; i ++)
	{
		if ((!ncel || (ncub <= ncel)) && (ncub < maxcub))
		{
			insertname (cubnames, emptyfiles [i],
				emptyposcub [i] + insertedcub ++, ncub ++);
			sout << "Note: The empty file '" << emptyfiles [i] <<
				"' is assumed to contain cubes.\n";
		}
		else if (ncel < maxcel)
		{
			insertname (celnames, emptyfiles [i],
				emptyposcel [i] + insertedcel ++, ncel ++);
			sout << "Note: The empty file '" << emptyfiles [i] <<
				"' is assumed to contain cells.\n";
		}
		else
		{
			sout << "WARNING: Too many empty files: "
				"ignoring '" << emptyfiles [i] << "'.\n";
		}
	}

	return 0;
} /* sortfiles */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// turn on a message that will appear if the program does not finish
	program_time = "Aborted after";

	// prepare user-configurable data
	char *filenames [] = {NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
		NULL, NULL};
	char *keepfilenames [] = {NULL, NULL, NULL, NULL};
	int namecount = 0, keepnamecount = 0;
	char *Xfinalname = NULL, *Yfinalname = NULL;
	char *XFinalname = NULL, *YFinalname = NULL;
	char *Xgenname = NULL, *Ygenname = NULL, *Fgenname = NULL;
	int genformat = 0;
	char *bettiname = NULL;
	char *savefiles = NULL;
	char *cubelist = NULL;
	short int runonly [8] = {0, 0, 0, 0, 0, 0, 0, 0};
	int runcount = 0;
	coordinate wrap [Cube::MaxDim];
	int wrapcount = 0;
	int levellist [Cube::MaxDim + 1], level [Cube::MaxDim + 1];
	int levelcount = 0;
	int i; // common variable for iterations - required by MSVC++
	for (i = 0; i < Cube::MaxDim; i ++)
	{
		wrap [i] = 0;
		level [i] = 0;
	}
	int p = 0;
	int memorylimit = -1;
	// acyclicity check: -1 = unnecessary (almost perfect map),
	// 0 = none, 1 = basic, 2 = thorough
	int checkacyclic = 1;
	bool indexmap = false;
	bool dontcollapse = false;
	bool fullgraph = false;
	bool suppressfullred = false;
	bool dontexpand = false;
	bool dontexpandF = false;
	bool obsolete_switch_e = false;
	bool oldoutput = false;
	bool dontaddfaces = false;
	bool verify = true;
	bool usetabulated = true;
	char *tabulated1d = 0;
	char *tabulated2d = 0;
	char *tabulated3d = 0;
	int runrand = 0;
	int hack = 0;

	// analyze the command line
	arguments a;
	arg (a, NULL, filenames, namecount, 10);
	arg (a, "k", keepfilenames, keepnamecount, 4);
	arg (a, "gf", genformat);
	arg (a, "g", Xgenname);
	arg (a, "g", Ygenname);
	arg (a, "g", Fgenname);
	arg (a, "b", bettiname);
	arg (a, "c", cubelist);
	arg (a, "w", wrap, wrapcount, Cube::MaxDim);
	arg (a, "l", levellist, levelcount, Cube::MaxDim + 1);
	arg (a, "m", memorylimit);
	arg (a, "s", savefiles, "");
	arg (a, "p", p);
	arg (a, "r", runonly, runcount, 8);
	arg (a, "t1", tabulated1d, "homcubes1d.bin");
	arg (a, "t2", tabulated2d, "homcubes2d.bin");
	arg (a, "t3", tabulated3d, "homcubes3d.bin");
	argswitch (a, "i", indexmap, true);
	argswitch (a, "d", dontaddfaces, true);
	// obsolete and temporary arguments
	arg (a, "f", Xfinalname);
	arg (a, "f", Yfinalname);
	arg (a, "F", XFinalname);
	arg (a, "F", YFinalname);
	arg (a, "-hack", hack, 1);
	arg (a, "-rand", runrand, 1);
	argswitch (a, "e", obsolete_switch_e, true);
	argswitch (a, "G", fullgraph, true);
	argswitch (a, "R", suppressfullred, true);
	argswitch (a, "C", dontcollapse, true);
	argswitch (a, "EF", dontexpandF, true);
	argswitch (a, "E", dontexpand, true);
	argswitch (a, "O", oldoutput, true);
	argswitch (a, "V", verify, false);
	argswitch (a, "T", usetabulated, false);
	argswitch (a, "A", checkacyclic, 0);
	argswitch (a, "a", checkacyclic, 2);
	argswitch (a, "a", checkacyclic, 2); // ignored
	argswitch (a, "B", MaxBddDim, 0); // external variable
	argswitch (a, "M", UseMalandainCode, true);
	// end of temporary switches
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's title
	#ifndef SIMPLIFIED
	if (argresult >= 0)
		sout << title << '\n';
	#endif

	// use not tabulated neighbor configurations
	if (!usetabulated)
	{
		tabulated. define (1, 0);
		tabulated. define (2, 0);
		tabulated. define (3, 0);
	}
	
	if (tabulated1d && (tabulated. read (1, tabulated1d) < 0))
	{
		tabulated. compute (1);
		tabulated. write (1, tabulated1d);
	}
	if (tabulated2d && (tabulated. read (2, tabulated2d) < 0))
	{
		tabulated. compute (2);
		tabulated. write (2, tabulated2d);
	}
	if (tabulated3d && (tabulated. read (3, tabulated3d) < 0))
	{
		tabulated. compute (3);
		tabulated. write (3, tabulated3d);
	}

	// make a correction to the maximal BDD dimension if necessary
	if (MaxBddDim > MaxBddDimPossible)
		MaxBddDim = MaxBddDimPossible;

	// ask the user not to use the old switch
	if (obsolete_switch_e)
		sout << "NOTE: Please, do not use the obsolete switch '-e' "
			"while invoking the program.\n"
			"The expansion of the other element of the pair "
			"is now turned on by default.\n";

	// adjust the run-only bits
	int runbits = runcount ? 0 : ~0;
	for (i = 0; i < runcount; i ++)
		if (runonly [i] > 0)
			runbits |= (0x01 << (runonly [i] - 1));
	if (suppressfullred)
		runbits &= ~(fulldimbit | expandAbit | expandFbit);
	if (dontexpand)
		runbits &= ~(expandAbit | expandFbit);
	if (dontexpandF)
		runbits &= ~expandFbit;

	// transform a list of levels to level bits
	for (i = 0; i < Cube::MaxDim + 1; i ++)
		level [i] = levelcount ? 0 : 1;
	for (i = 0; i < levelcount; i ++)
	{
		if ((levellist [i] >= 0) && (levellist [i] <= Cube::MaxDim))
			level [levellist [i]] = 1;
		else
		{
			sout << "Requested homology level " <<
				levellist [i] << " is out of range.\n";
			argresult = -1;
			break;
		}
	}

	// set the space wrapping if necessary
	if (wrapcount == 1)
		PointBase::setwrapping (wrap [0]);
	else if (wrapcount)
		PointBase::setwrapping (wrap);

	// set the final cubes file names
	if (XFinalname)
	{
		Xfinalname = XFinalname;
		runbits = 0x01;
	}
	if (YFinalname)
	{
		Yfinalname = YFinalname;
		runbits = 0x01;
	}

	// set real filenames to what was read from the command line
	// the order of the names is: X, A, Y, B
	char *cubnames [] = {NULL, NULL, NULL, NULL};
	char *celnames [] = {NULL, NULL, NULL, NULL};
	char *mapname = NULL;
	if (!namecount)
		argresult = 1;
	if (!argresult)
	{
		// split file names to appropriate tables
		int ncub = 4, ncel = 4;
		bool almostperfect = false;
		try
		{
			if (splitfiles (filenames, namecount, cubnames, ncub,
				celnames, ncel, &mapname, &almostperfect) < 0)
				argresult = -1;
		}
		catch (const char *msg)
		{
			sout << "ERROR: " << msg << '\n';
			argresult = -1;
		}

		// turn off acyclicity verification for almost perfect maps
		if (almostperfect && (checkacyclic < 2))
		{
			sout << "Note: The map seems to be almost perfect: "
				"Turning off acyclicity verification.\n";
			checkacyclic = -1;
		}

		// adjust file names for "F.map Y.cub" or "F.map -i A.cub"
		if (mapname && (ncub == 1) && (ncel == 0))
		{
			cubnames [indexmap ? 1 : 2] = cubnames [0];
			cubnames [0] = NULL;
		}
		// adjust file names for "F.map X.cub Y.cub"
		else if (mapname && (ncub == 2) && (ncel == 0) && !indexmap)
		{
			cubnames [2] = cubnames [1];
			cubnames [1] = NULL;
		}
		// adjust file names for "F.map A.cub Y.cub B.cub"
		else if (mapname && (ncub == 3) && (ncel == 0))
		{
			for (int i = 2; i > 0; i --)
				cubnames [i] = cubnames [i - 1];
			cubnames [0] = NULL;
		}
	}
	char *Xcubname = cubnames [0], *Acubname = cubnames [1],
		*Ycubname = cubnames [2], *Bcubname = cubnames [3];
	char *Xcelname = celnames [0], *Acelname = celnames [1],
		*Ycelname = celnames [2], *Bcelname = celnames [3];

	// split file names to keep to cubes and cells
	char *keepcubnames [] = {NULL, NULL};
	char *keepcelnames [] = {NULL, NULL};
	if (!argresult)
	{
		// sort file names to appropriate tables
		int ncub = 2, ncel = 2;
		if (splitfiles (keepfilenames, keepnamecount,
			keepcubnames, ncub, keepcelnames, ncel) < 0)
			argresult = -1;
	}
	char *Xkeepcubname = keepcubnames [0],
		*Ykeepcubname = keepcubnames [1];
	char *Xkeepcelname = keepcelnames [0],
		*Ykeepcelname = keepcelnames [1];

	// warn if an index map was requested, but there is no map
	if (!argresult && !mapname && indexmap)
	{
		indexmap = false;
		sout << "WARNING: Ignoring '-i', because not working "
			"with a map.\n";
	}

	// warn if deprecated command-line arguments were used
//	if (Xfinalname || Yfinalname)
//		sout << "WARNING: A deprecated argument '-f' or '-F' "
//			"was used. Plase, use '-s' and '-r' instead.\n";

	// warn if there are too many names for files with generators
	if (!mapname && (Ygenname || Fgenname))
	{
		Ygenname = NULL;
		Fgenname = NULL;
		sout << "WARNING: Ignoring superfluous -g argument(s), "
			"because not working with a map.\n";
	}

	// warn if some generators are going to be discarded and some are not
	if (mapname && Xgenname && !Ygenname)
		sout << "WARNING: Generators of map's codomain "
			"will be discarded.\n";

	// warn if an unnecessary file name was given
	if (!mapname && (Ykeepcubname || Ykeepcelname))
	{
		Ykeepcubname = NULL;
		Ykeepcelname = NULL;
		sout << "WARNING: Ignoring superfluous -k argument(s), "
			"because not working with a map.\n";
	}

	// adjust the ring of integers modulo p if requested for
	if (p > 0)
		integer::initialize (p);

	// set the memory limit for the bit field sets
	if (memorylimit >= 0)
		knownbits. setkblimit (1024 * memorylimit);

	#ifdef SIMPLIFIED
	// make the simplified program display no output at all
	if (!argresult)
	{
		scon. show = false;
		sout. show = false;
		program_time = sout;
	}
	#endif

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// show some technical information on various limits
	sbug << "[Tech info: " <<
		"coord " << sizeof (coordinate) << ", " <<
		"cube " << sizeof (cube) << ", " <<
		"qcell " << sizeof (qcell) << ", " <<
		"int_t " << sizeof (int_t) << ", " <<
		"int " << sizeof (int) << ", " <<
		"long " << sizeof (long) << ", " <<
		"addr " << sizeof (int *) << ",\n" <<
		"DimBits " << DimBits << ", " <<
		"NumMask " << NumMask << ", " <<
		"MaxBasDim " << MaxBasDim << ".]\n";

	// if help requested or no filenames present, show help information
	if (argresult > 0)
	{
		#ifdef SIMPLIFIED
		sout << title << '\n';
		#endif
		sout << helpinfo << '\n';
		return 1;
	}

	// use the random numbers generator a few times to change the order
	// of reductions (this is a temporary hack to overcome some errors)
	for (int i = 0; i < runrand; ++ i)
		std::rand ();

	// try running the main function and catch an error message if thrown
	int result = 0;
	try
	{
		homcubes (mapname, Xcubname, Acubname, Ycubname, Bcubname,
			Xcelname, Acelname, Ycelname, Bcelname,
			Xkeepcubname, Ykeepcubname, Xkeepcelname,
			Ykeepcelname, savefiles, Xfinalname, Yfinalname,
			Xgenname, Ygenname, Fgenname, genformat,
			bettiname, cubelist, level, indexmap,
			checkacyclic, dontaddfaces, fullgraph, dontcollapse,
			runbits, verify, oldoutput, hack);
		sseq << "P \"The end.\"\n";
		scon << "Thank you for using this software. "
			"We appreciate your business.\n";
	}
	catch (const char *msg)
	{
		#ifdef SIMPLIFIED
		sout. show = true;
		#endif
		sout << "ERROR: " << msg << '\n';
		result = -1;
	}
	catch (const std::exception &e)
	{
		#ifdef SIMPLIFIED
		sout. show = true;
		#endif
		sout << "ERROR: " << e. what () << '\n';
		return -1;
	}
	catch (...)
	{
		#ifdef SIMPLIFIED
		sout. show = true;
		#endif
		sout << "ABORT: An unknown error occurred.\n";
		result = -1;
	}

	return result;
} /* main */


// --------------------------------------------------
// -------------------- HISTORY ---------------------
// --------------------------------------------------

// 0.00 (December 10, 1997)
//      - a rough sketch of the main algorithm
// 0.01 (December 14, 1997)
//      - the first version of the program
// 1.00 (May 30, 1999)
//      - final version (part of my master thesis in computer science)
// 2.00 (December 26, 1999)
//      - a new version of "chains" (coefficients in a Euclidean domain)
// 2.01 (February 9, 2000)
//      - wrapping of the space added
// 2.05 (May 10, 2000)
//      - reduction changed, -sr option added, -sf doesn't save kept cubes
// 2.06 (October 11, 2000)
//      - a bug in simple_form fixed (the program is now much faster)
// 2.07 (December 1, 2001)
//      - improved contraction: use of stack added
// 2.08 (March 8-23, 2002)
//      - a template version of "chains.h", "arg.h" used to read command line
// 2.99 (March 24, 2002)
//      - a completely new approach to cubes, cubical cells and reduction
//      - computation of the map induced in homology by a multivalued cubical
//        acyclic map according to an idea by Professor Marian Mrozek
// 3.00 (November 13-22, 2002)
//      - a new, less restrictive approach to the homology of maps
// 3.01 (December, 2002)
//      - improved reduction, expansion of A in X for maps
// 3.02 (January 24-26, 2003)
//      - inverting the inclusion map
// 3.03 (February 12 - May 1, 2003)
//      - more flexibility (command-line, saving partial results, etc.)
// 3.04 (May 4, 2003)
//      - keeping the map acyclic while reducing its domain
// 3.05 (Sep 10, 2003)
//      - acyclicity verification command-line arguments re-arranged

/// @}

