/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file homcub2l.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in December 1997. Last revision: June 11, 2008.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
#include "capd/homology/localvar.h"
#include "capd/homology/homtools.h"
#include "capd/homology/twolayer.h"

#include <exception>
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

const char *title = "\
HOMCUB2L, ver. 0.01, 06/11/08. Copyright (C) 1997-2010 by Pawel Pilarczyk.\n\
This is free software. No warranty. Consult 'license.txt' for details.";

const char *helpinfo = "\
This program computes the homological Conley index map with the use\n\
of two-layer cubical sets, as described in the paper by P. Pilarczyk\n\
and K. Stolot, `Excision-preserving cubical approach to the algorithmic\n\
computation of the discrete Conley index'.\n\
Call with:\n\
F.map X.cub A.cub - for (F \\circ i^{-1})_*: (X+A, A) -> (X+A, A),\n\
Switches and additional arguments:\n\
-c file - read through this file first to fix the right numbers of cubes,\n\
-s prefix - save intermediate data; add the given prefix to file names,\n\
-m n - use at most n megabytes of memory for bit fields while reducing,\n\
-w n - wrap the space (repeat for each axis, use 0 for no space wrapping),\n\
-p n - perform the computations in the field of integers modulo prime n,\n\
-a - ensure that map's acyclicity is preserved during reduction (slow),\n\
-h - display this brief help information only and exit.\n\
Other switches (for debug and tests; may be removed or changed soon):\n\
-R - don't reduce fulldim, -G - use full graph, -C - don't collapse faces,\n\
-E - don't expand (X,A), -A - don't check map's acyclicity, -B - no BDDs,\n\
-V - don't verify the assumptions on the cubical map (must use chkmvmap),\n\
For more information consult the accompanying documentation (if available)\n\
or ask the program's author at http://www.PawelPilarczyk.com/.";


// --------------------------------------------------
// -------------------- HOMCUBES --------------------
// --------------------------------------------------

static int exithom (const char *message, const char *bettiname = 0)
{
	sout << message << '\n';
	program_time = "Time used:";
	return 0;
} /* exithom */

inline int setlayer (SetOfCubes2l &X, int layer)
{
	int_t n = X. size ();
	SetOfCubes2l Y;
	for (int_t i = 0; i < n; ++ i)
	{
		Cube2l q = X [i];
		q. layer (layer);
		Y. add (q);
	}
	Y. swap (X);
	return 0;
} /* setlayer */

inline int setlayer (CombinatorialMultivaluedMap2l &F, int layer)
{
	const SetOfCubes2l &X = F. getdomain ();
	int_t domsize = X. size ();
	CombinatorialMultivaluedMap2l Fl;
	for (int_t i = 0; i < domsize; ++ i)
	{
		Cube2l q = X [i];
		const SetOfCubes2l &img = F (q);
		int_t imgsize = img. size ();
		q. layer (layer);
		for (int_t j = 0; j < imgsize; ++ j)
		{
			Cube2l r = img [j];
			r. layer (layer);
			Fl [q]. add (r);
		}
	}
	Fl. swap (F);
	return 0;
} /* setlayer */

static int homcub2l (const char *mapname,
	const char *Xcubname, const char *Acubname,
	const char *cubelist, const char *savefiles,
	int checkacyclic, bool dontaddfaces, bool fullgraph, bool dontexpand,
	bool dontreduce, bool dontcollapse, bool verify)
{
	// turn off locally the usage of binary decision diagrams
	local_var<int> TurnOffMaxBddDim (MaxBddDim, 0);

	// make sure all levels are computed
	int *level = 0;

	// read through the list of cubes to establish the right cube numbers
	// if the representation of cubes by numbers is going to be used
	scancubes<Cube> (cubelist);

	// ----- read the sets of cubes -----

	// read the set of cubes X
	SetOfCubes Xcubes0;
	readelements (Xcubname, Xcubes0, "X");

	// read the set of cubes A
	SetOfCubes Acubes0;
	readelements (Acubname, Acubes0, "A");

	// remove from X cubes which are in A
	removeAfromX (Xcubes0, Acubes0, "X", "A");

	// leave in A only the neighbors of X\\A
	restrictAtoneighbors (Xcubes0, Acubes0, "X", "A");

	// if the set X is empty, the answer is obvious
	if (Xcubname && Xcubes0. empty ())
		return exithom ("X is a subset of A. "
			"The homology of (X,A) is trivial "
			"and the map is 0.");

	// ----- define the layers ------

	// define the two-layer structure
	sout << "Defining the two-layer structure... ";
	Cube2l::setlayers (Xcubes0, Acubes0);

	// transform the cubes in X and in A to the two-layer sets
	SetOfCubes2l Xcubes;
	for (int_t i = 0; i < Xcubes0. size (); ++ i)
		Xcubes. add (Cube2l (Xcubes0 [i], 1));
	SetOfCubes2l Acubes;
	for (int_t i = 0; i < Acubes0. size (); ++ i)
		Acubes. add (Cube2l (Acubes0 [i], 0));

	// forget the initial single-layer sets
	{
		SetOfCubes empty;
		Xcubes0 = empty;
		Acubes0 = empty;
	}

	// say that defining the two-layer structure is done
	sout << Cube2l::layer1 (). size () << "+" <<
		Cube2l::layer0 (). size () << " cubes, " <<
		CubicalCell2l::identify (). size () << " cells.\n";

	// ----- read the map ------

	// determine Y and B
	SetOfCubes2l Ycubes (Xcubes);
	SetOfCubes2l Bcubes (Acubes);
	SetOfCubes2l XAcubes (Xcubes);
	XAcubes. add (Acubes);
	readmapimage (mapname, XAcubes, "X", Bcubes);
	{
		SetOfCubes2l empty;
		XAcubes = empty;
	}
	sout << "Creating the sets Y and B... ";
	Bcubes. remove (Ycubes);
	sout << Ycubes. size () << " cubes in Y\\B, " <<
		Bcubes. size () << " in B.\n";

	// check that no cube that was added to B is contained in X\A
//	for (int_t i = Acubes. size (); i < Bcubes. size (); ++ i)
//		if (Xcubes. check (Bcubes [i]))
//			throw ("The map is invalid: The image of A "
//				"intersects X\\A.");

	// remember the original size of the set A and of the set X
	int_t origAsize = Acubes. size ();
	int_t origXsize = Xcubes. size ();

	// determine the dimension of X and Y if possible
	int Xspacedim = Xcubes. empty () ? -1 : Xcubes [0]. dim ();
	int Yspacedim = Ycubes. empty () ? -1 : Ycubes [0]. dim ();

	// ----- reduce the sets of cubes -----

	// prepare the set of cubes to keep in X (unused in this program)
	SetOfCubes2l Xkeepcubes;

	// allocate a suitable bit field set for the reduction and show msg
	if (Xspacedim > 0)
		knownbits [Xspacedim];

	// reduce the pair of sets of cubes (X,A) without acyclicity check
	if (!dontreduce && !Acubes. empty () && (checkacyclic < 2))
	{
		// reduce the pair (X,A)
		reducepair (Xcubes, Acubes, Xkeepcubes, "X", "A");

		// if nothing remains in X, then the result is trivial
		if (Xcubes. empty ())
			return exithom ("There are no cubes left "
				"in X\\A. The homology of (X,A) "
				"is trivial and the map is 0.");
	}

	// remember which inclusions have been verified
	bool inclFABchecked = false;
	bool inclFXYchecked = false;

	// read the map on X or only on X\A for careful or extended reduction
	CombinatorialMultivaluedMap2l FcubmapT;
	if (checkacyclic > 1)
	{
		readmaprestriction (FcubmapT, mapname, Xcubes, Acubes, "X",
			"for careful reduction");
		// check if F (X\A) \subset Y
		if (verify)
		{
			checkimagecontained (FcubmapT,
				Xcubes, Ycubes, Bcubes,
				Acubes. empty () ? "X" : "X\\A", "Y");
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
	else if (!Acubes. empty ())
	{
		readmaprestriction (FcubmapT, mapname, Xcubes,
			Acubes. empty () ? "X" : "X\\A",
			"for extended reduction");
		// check if F (X\A) \subset Y
		if (verify)
		{
			checkimagecontained (FcubmapT,
				Xcubes, Ycubes, Bcubes,
				Acubes. empty () ? "X" : "X\\A", "Y");
			inclFXYchecked = true;
		}
	}

	// expand A within X and modify (Y,B) if requested to
	if (!dontexpand && !Acubes. empty ())
	{
		// expand A towards X and modify (Y,B) accordingly
		expandAinX (Xcubes, Acubes, Ycubes, Bcubes, FcubmapT,
			"X", "A", "B", true /*indexmap*/, checkacyclic > 1);
	}

	// reduce the pair (X,A) or the set X with acyclicity check
	if (!dontreduce && (checkacyclic > 1))
	{
		// leave in A only the neighbors of X\\A
		restrictAtoneighbors (Xcubes, Acubes, "X", "A");

		// reduce the pair (X,A) with acyclicity check
		reducepair (Xcubes, Acubes, FcubmapT, Xkeepcubes, "X", "A");

		// if nothing remains in X, then the result is trivial
		if (Xcubes. empty ())
			return exithom ("There are no cubes left "
				"in X\\A. The homology of (X,A) "
				"is trivial and the map is 0.");
	}

	// release the memory used by the map as no longer necessary
	CombinatorialMultivaluedMap2l empty;
	FcubmapT = empty;

	// reduce the pair (X,A) even further
	if (!dontreduce && (checkacyclic < 2) && !Acubes. empty ())
	{
		// leave in A only the neighbors of X\\A
		restrictAtoneighbors (Xcubes, Acubes, "X", "A");

		// continue the reduction of the pair (X,A)
		reducepair (Xcubes, Acubes, Xkeepcubes, "X", "A");
	}

	// save the cubes left in X and A after the reduction
	if (Xcubname)
		savetheset (Xcubes, savefiles, "x.cub",
			Acubname ? "the cubes in X\\A after reduction" :
			"the cubes in X after reduction");
	if (Acubname)
		savetheset (Acubes, savefiles, "a.cub",
			"the cubes in A after reduction");

	// indicate that the acyclicity of the map should be verified
	if (checkacyclic >= 0)
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

	// read the map restricted to X\A
	CombinatorialMultivaluedMap2l Fcubmap;
	readmaprestriction (Fcubmap, mapname, Xcubes,
		Acubes. empty () ? "X" : "X\\A");

	// check if F (X\A) \subset Y
	if (verify && !inclFXYchecked)
	{
		checkimagecontained (Fcubmap, Xcubes, Ycubes, Bcubes,
			Acubes. empty () ? "X" : "X\\A", "Y");
		inclFXYchecked = true;
	}

	// read the map restricted to A
	CombinatorialMultivaluedMap2l FcubmapA;
	readmaprestriction (FcubmapA, mapname, Acubes, "A");

	// check if F (A) \subset B [this should always be satisfied]
	if (verify && !inclFABchecked && !Acubes. empty ())
	{
		checkimagecontained (FcubmapA, Acubes, Bcubes, "A", "B");
		checkimagedisjoint (FcubmapA, Acubes, Ycubes, "A", "Y\\B");
		inclFABchecked = true;
	}

	// set the union of the domain of the map of interest
	// and the image of the map as the cubes to keep in Y
	SetOfCubes2l Ykeepcubes;
	addmapimg (Fcubmap, FcubmapA, Xcubes, Acubes, Ykeepcubes,
		true /*indexmap*/);

	// reduce the pair of cubical sets (Y,B) towards the image of F
	if (!dontreduce && (Xspacedim == Yspacedim))
	{
		if (!dontexpand)
			expandAinX (Ycubes, Bcubes, "Y", "B");
		restrictAtoneighbors (Ycubes, Bcubes, "Y", "B", &Ykeepcubes);
		reducepair (Ycubes, Bcubes, Ykeepcubes, "Y", "B");
	}

	// save the cubes left in Y and B after the reduction
	savetheset (Ycubes, savefiles, "y.cub",
		"the cubes in Y\\B after reduction");
	savetheset (Bcubes, savefiles, "b.cub",
		"the cubes in B after reduction");

	// show how many bit fields were in use and forget the bit fields now
	if (checkacyclic <= 0)
		knownbits. forget ();

	// ----- read or create the cubical complexes -----

	// transform the set of cubes X into a set of cells and forget Xcubes
	CubicalComplex2l Xcompl;
	cubes2cells (Xcubes, Xcompl, Acubes. size () ? "X\\A" : "X");
	if (Xcubes. size ())
	{
		SetOfCubes2l empty;
		Xcubes = empty;
	}

	// transform the set of cubes A into a set of cubical cells
	CubicalComplex2l Acompl;
	cubes2cells (Acubes, Acompl, "A");
	if (Acubes. size ())
	{
		SetOfCubes2l empty;
		Acubes = empty;
	}

	// if the set X is empty, no computations are necessary
	if (Xcompl. empty ())
	{
		if (!Acompl. empty ())
		{
			return exithom ("The set X is contained in A. "
				"The homology of (X,A) is trivial.");
		}
		else
		{
			return exithom ("The set X is empty. "
				"The homology of X is trivial.");
		}
	}

	// transform the cubes in Y into cubical cells and forget the cubes
	CubicalComplex2l Ycompl;
	cubes2cells (Ycubes, Ycompl, Bcubes. empty () ? "Y" : "Y\\B");
	if (!Ycubes. empty ())
	{
		SetOfCubes2l empty;
		Ycubes = empty;
	}

	// transform the cubes in B into cubical cells and forget the cubes
	CubicalComplex2l Bcompl;
	cubes2cells (Bcubes, Bcompl, "B");
	if (!Bcubes. empty ())
	{
		SetOfCubes2l empty;
		Bcubes = empty;
	}

	// transform the cubes to keep in Y into cells and forget the cubes
	CubicalComplex2l Ykeepcompl;
	if (!dontcollapse)
		cubes2cells (Ykeepcubes, Ykeepcompl, "Ykeep");
	if (!Ykeepcubes. empty ())
	{
		SetOfCubes2l empty;
		Ykeepcubes = empty;
	}

	// determine the dimension of X and Y as cubical complexes
	int Xdim = Xcompl. dim ();
	if ((Xspacedim < 0) && (Xdim >= 0))
		Xspacedim = Xcompl [Xdim] [0]. spacedim ();
	int Ydim = Ycompl. dim ();
	if ((Yspacedim < 0) && (Ydim >= 0))
		Yspacedim = Ycompl [Ydim] [0]. spacedim ();

	// ----- collapse the cubical sets (X,A) -----

	// create a full cubical complex (with all the faces) of X\A
	if (dontcollapse)
	{
		// decrease the dimension of A to the dimension of X
		decreasedimension (Acompl, Xdim, "A");

		// add boundaries to cells in X and A
		addboundaries (Xcompl, Acompl, 0, !!mapname, "X", "A");
	}

	// create an empty set of cells to keep in X
	CubicalComplex2l Xkeepcompl;

	// reduce the pair of sets (Xcompl, Acompl) while adding to them
	// boundaries of all the cells
	if (!dontcollapse)
	{
		collapse (Xcompl, Acompl, Xkeepcompl, "X", "A",
			!dontaddfaces, mapname && !fullgraph,
			!mapname, level);

		// if nothing remains in X, then the result is trivial
		if (Xcompl. empty ())
			return exithom ("Nothing remains in X. "
				"The homology of (X,A) is trivial.");
	}

	// forget the cells to keep in X
	if (!Xkeepcompl. empty ())
	{
		CubicalComplex2l empty;
		Xkeepcompl = empty;
	}

	// make a correction to the dimension of X
	if (Xdim != Xcompl. dim ())
	{
		sout << "Note: The dimension of X decreased from " <<
			Xdim << " to " << Xcompl. dim () << ".\n";

		Xdim = Xcompl. dim ();
	}

	// save the cells left in X and A after the reduction
	savetheset (Xcompl, savefiles, "x.cel",
		"the cells in X\\A after reduction");
	savetheset (Acompl, savefiles, "a.cel",
		"the cells in A after reduction");

	// ----- create a reduced graph of F -----

	// create the map F defined on the cells in its domain
	mvcellmap<CubicalCell2l,integer,Cube2l> Fcellcubmap (Xcompl);
	{
		sout << "Creating the map F on cells in X... ";
		int_t count = createimages (Fcellcubmap, Fcubmap, FcubmapA);
		sout << count << " cubes added.\n";
	}

	// create the map F defined on the cells in its domain subcomplex A
	mvcellmap<CubicalCell2l,integer,Cube2l> FcellcubmapA (Acompl);
	if (!Acompl. empty ())
	{
		sout << "Creating the map F on cells in A... ";
		int_t count = createimages (FcellcubmapA, FcubmapA);
		sout << count << " cubes added.\n";
	}

	// show how many bit fields were in use and forget the bit fields now
	knownbits. forget ();

	// create the full graph of F on A if requested
	CubicalComplex2l FcomplA;
	if (fullgraph && !Acompl. empty ())
	{
		sout << "Creating the full graph of F|A... ";
		int_t prevA = FcomplA. size ();
		creategraph (FcellcubmapA, FcomplA, dontcollapse);
		sout << (FcomplA. size () - prevA) << " cells added.\n";
	}

	// create the full graph of F on X if requested
	CubicalComplex2l Fcompl;
	if (fullgraph)
	{
		sout << "Creating the full graph of F... ";
		int_t prev = Fcompl. size ();
		creategraph (Fcellcubmap, FcomplA, Fcompl, dontcollapse);
		sout << (Fcompl. size () - prev) << " cells added.\n";

		// forget 'FcomplA' if it is not going to be used anymore
		if (dontcollapse && !FcomplA. empty ())
		{
			CubicalComplex2l empty;
			FcomplA = empty;
		}
	}

	// create the graph of F as a cubical cell complex
	if (!fullgraph)
	{
		sout << "Creating a cell map for F... ";
		mvcellmap<CubicalCell2l,integer,CubicalCell2l>
			Fcellmap (Xcompl);
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
		savetheset (Fcellmap, savefiles, "f.clm",
			"the reduced cell map for F");

		sout << "Creating the graph of F... ";
		int_t prev = Fcompl. size ();
		creategraph (Fcellmap, Fcompl, false);
		sout << (Fcompl. size () - prev) << " cells added.\n";
	}

	// reduce the graph of F by free face collapses
	if (!dontcollapse && fullgraph)
	{
		int olddim = Fcompl. dim ();
		sout << "Collapsing the graph of F... ";
		CubicalComplex2l empty;
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
			CubicalComplex2l empty;
			FcomplA = empty;
		}
	}

	// save the created graph of F if requested to
	savetheset (Fcompl, savefiles, "f.cel", "the reduced graph of F");

	// forget the cubical map on the cells
	{
		mvcellmap<CubicalCell2l,integer,Cube2l> empty;
		Fcellcubmap = empty;
		FcellcubmapA = empty;
	}

	// ----- collapse the cubical sets (Y,B) -----

	// decrease the dimension of B to the dimension of Y
	decreasedimension (Bcompl, Ydim, "B");

	// create a full cubical complex (with all the faces) of Y\B
	if (!Ycompl. empty ())
	{
		if (!dontaddfaces)
			addboundaries (Ycompl, Bcompl, 0, false, "Y", "B");

		// forget the cubical complex of B
		if (!Bcompl. empty ())
		{
			sout << "Forgetting " << Bcompl. size () <<
				" cells from B.\n";
			CubicalComplex2l empty;
			Bcompl = empty;
		}
	}

	// collapse the codomain of the map towards the image of F
	if (!dontcollapse)
	{
		sout << "Computing the image of F... ";
		int_t prev = Ykeepcompl. size ();
		project (Fcompl, Ykeepcompl, Ycompl, Xspacedim, Yspacedim,
			0, level, false);
		project (Fcompl, Ykeepcompl, Ycompl, 0, Xspacedim,
			Yspacedim, level, false);
		sout << (Ykeepcompl. size () - prev) << " cells added.\n";

		// for debug purposes only (hack?)
	//	savetheset (Ykeepcompl, savefiles, "f_img.cel",
	//		"the image of F (and i)");
	//	savetheset (Ycompl, savefiles, "y_nonred.cel",
	//		"the cells in Y before the reduction");

		sout << "Collapsing Y towards F(X)... ";
		CubicalComplex2l empty;
		int_t count = Ycompl. collapse (empty, Ykeepcompl,
			0, 0, 0, level);
		sout << 2 * count << " cells removed, " << Ycompl. size () <<
			" left.\n";
	}

	// forget the cells to keep in Y
	if (!Ykeepcompl. empty ())
	{
		CubicalComplex2l empty;
		Ykeepcompl = empty;
	}

	// save the cells left in Y and B after the reduction
	savetheset (Ycompl, savefiles, "y.cel",
		"the cells in Y\\B after reduction");
	savetheset (Bcompl, savefiles, "b.cel",
		"the cells in B after reduction");

	// make a correction to the dimension of Y
	if (Ydim != Ycompl. dim ())
	{
		sout << "Note: The dimension of Y decreased from " <<
			Ydim << " to " << Ycompl. dim () << ".\n";

		Ydim = Ycompl. dim ();
		for (int i = Ydim + 1; level && (i < Cube2l::MaxDim); i ++)
			if (i > Xdim)
				level [i] = 0;
	}

	// ----- create chain complexes from the cubical sets ------

	// create a chain complex from X (this is a relative chain complex!)
//	chaincomplex<integer> cx (Xcompl. dim (), false /*generators*/);

	// create a chain complex from the graph of F (it is relative)
	chaincomplex<integer> cgraph (Fcompl. dim (), false);
	sout << "Creating the chain complex of the graph of F... ";
	createchaincomplex (cgraph, Fcompl);
	sout << "Done.\n";
	savetheset (cgraph, savefiles, "f.chn",
		"the chain complex of the graph of F");

	// create the chain complex from Y (this is a relative complex)
	chaincomplex<integer> cy (Ydim, false);
	sout << "Creating the chain complex of Y... ";
	createchaincomplex (cy, Ycompl);
	sout << "Done.\n";
	savetheset (cy, savefiles, "y.chn", "the chain complex of (Y,B)");

	// create the projection map from the graph of the map to Y
	chainmap<integer> cmap (cgraph, cy);
	sout << "Creating the chain map of the projection... ";
	createprojection (Fcompl, Ycompl, cmap, Xspacedim,
		Yspacedim, 0, level);
	sout << "Done.\n";
	savetheset (cmap, savefiles, "f.chm", "the chain map of F");

	// if this is an index map, create the projection map from the graph
	// of the map to X composed with the inclusion into Y
	chainmap<integer> imap (cgraph, cy);
	sout << "Creating the chain map of the inclusion... ";
	createprojection (Fcompl, Ycompl, imap, 0, Xspacedim,
		Yspacedim, level);
	sout << "Done.\n";
	savetheset (imap, savefiles, "i.chm",
		"the chain map of the inclusion");

	// forget the graph of F if it is not going to be used anymore
	if (!Fcompl. empty ())
	{
		CubicalComplex2l empty;
		Fcompl = empty;
	}

	// forget the coordinates of cubes if they are not needed anymore
	PointBase::showused (sout);
	PointBase::forget ();

	// show how much time was used for the reduction
	program_time. show ("Time used so far:");

	// ----- compute and show homology, save generators -----

	// compute the homology of the chain complex of X
//	chain<integer> *hom_cx;

	// compute the homology of the chain complex of the graph of the map
	chain<integer> *hom_cgraph;
	sout << "Computing the homology of the graph of F over " <<
		integer::ringname () << "...\n";
	cgraph. compute_and_show_homology (sout, hom_cgraph, level);

	// compute the homology of the chain complex of Y
	chain<integer> *hom_cy;
	sout << "Computing the homology of Y over " <<
		integer::ringname () << "...\n";
	cy. compute_and_show_homology (sout, hom_cy, level);

	// ----- show the map(s) -----

	// determine the maximal non-trivial homology level for maps
	int homdimgraph = cgraph. dim ();
	while ((homdimgraph >= 0) && (!hom_cgraph [homdimgraph]. size ()))
		homdimgraph --;
	int homdimy = cy. dim ();
	while ((homdimy >= 0) && (!hom_cy [homdimy]. size ()))
		homdimy --;
//	sout << "Maximal homology level considered for the map "
//		"is " << homdim << ".\n";

	// prepare the data structures for the homology
	chaincomplex<integer> hgraph (homdimgraph);
	chaincomplex<integer> hy (homdimy);
	chainmap<integer> hmap (hgraph, hy);
	chainmap<integer> hincl (hgraph, hy);
	chainmap<integer> hcomp (hgraph, hgraph);

	// show the map induced in homology by the chain map
	sout << "The map induced in homology is as follows:\n";
	hgraph. take_homology (hom_cgraph);
	hy. take_homology (hom_cy);
	hmap. take_homology (cmap, hom_cgraph, hom_cy);
	hmap. show (sout, "\tf", "x", "y", level);

	// show the map induced in homology by the inclusion map
	sout << "The map induced in homology by the inclusion:\n";
	hincl. take_homology (imap, hom_cgraph, hom_cy);
	hincl. show (sout, "\ti", "x", "y", level);

	sout << "The inverse of the map induced by the inclusion:\n";
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
	}

	if (invertible)
	{
		hincl. show (sout, "\tI", "y", "x", level);

		sout << "The composition of F and the inverse "
			"of the map induced by the inclusion:\n";
		hcomp. compose (hincl, hmap);
		hcomp. show (sout, "\tF", "x", "x", level);
	}

	program_time. show ("Total time used:");
	program_time = 0;
	scon << "[Press Ctrl-C to exit.]\r";
	return 0;
} /* homcub2l */


// --------------------------------------------------
// ---------------------- MAIN ----------------------
// --------------------------------------------------

int main (int argc, char *argv [])
// Return: 0 = Ok, -1 = Error, 1 = Help displayed, 2 = Wrong arguments.
{
	// turn on a message that will appear if the program does not finish
	program_time = "Aborted after";

	// prepare user-configurable data
	char *Fname = NULL, *Xname = NULL, *Aname = NULL;
	char *savefiles = NULL;
	char *cubelist = NULL;
	coordinate wrap [Cube2l::MaxDim];
	int wrapcount = 0;
	int i; // common variable for iterations - required by MSVC++
	for (i = 0; i < Cube2l::MaxDim; i ++)
		wrap [i] = 0;
	int p = 0;
	int memorylimit = -1;
	// acyclicity check: -1 = unnecessary (almost perfect map),
	// 0 = none, 1 = basic, 2 = thorough
	int checkacyclic = 1;
	bool dontreduce = false;
	bool dontcollapse = false;
	bool fullgraph = false;
	bool dontexpand = false;
	bool dontaddfaces = false;
	bool verify = true;

	// analyze the command line
	arguments a;
	arg (a, 0, Fname);
	arg (a, 0, Xname);
	arg (a, 0, Aname);
	arg (a, "c", cubelist);
	arg (a, "w", wrap, wrapcount, Cube2l::MaxDim);
	arg (a, "m", memorylimit);
	arg (a, "s", savefiles, "");
	arg (a, "p", p);
	// obsolete and temporary arguments
	argswitch (a, "G", fullgraph, true);
	argswitch (a, "R", dontreduce, true);
	argswitch (a, "C", dontcollapse, true);
	argswitch (a, "E", dontexpand, true);
	argswitch (a, "V", verify, false);
	argswitch (a, "A", checkacyclic, 0);
	argswitch (a, "B", MaxBddDim, 0); // external variable
	argswitch (a, "a", checkacyclic, 2);
	argswitch (a, "a", checkacyclic, 2);	// ignored
	// end of temporary switches
	arghelp (a);

	argstreamprepare (a);
	int argresult = a. analyze (argc, argv);
	argstreamset ();

	// show the program's title
	if (argresult >= 0)
		sout << title << '\n';

	// set the space wrapping if necessary
	if (wrapcount == 1)
		PointBase::setwrapping (wrap [0]);
	else if (wrapcount)
		PointBase::setwrapping (wrap);

	// adjust the ring of integers modulo p if requested for
	if (p > 0)
		integer::initialize (p);

	// set the memory limit for the bit field sets
	if (memorylimit >= 0)
		knownbits. setkblimit (1024 * memorylimit);

	// if something was incorrect, show an additional message and exit
	if (argresult < 0)
	{
		sout << "Call with '--help' for help.\n";
		return 2;
	}

	// if help requested or no filenames present, show help information
	if ((argresult > 0) || (!Aname))
	{
		sout << helpinfo << '\n';
		return 1;
	}

	// try running the main function and catch an error message if thrown
	try
	{
		homcub2l (Fname, Xname, Aname, cubelist, savefiles,
			checkacyclic, dontaddfaces, fullgraph, dontexpand,
			dontreduce, dontcollapse, verify);
		scon << "Thank you for using this software. "
			"We appreciate your business.\n";
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

