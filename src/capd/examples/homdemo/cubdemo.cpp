/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubdemo.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on February 15, 2003. Last revision: July 27, 2004.


#include "cubdemo.h"

#include <iostream>
#include <fstream>


// --------------------------------------------------
// -------------------- READ MAP --------------------
// --------------------------------------------------

void readmap (const char *filename, cubicalmap &F, const char *name)
{
	sout << "Reading " << name << " from '" << filename << "'... ";
	std::ifstream in (filename);
	if (!in)
		fileerror (filename);
	in >> F;
	sout << "Done.\n";
	return;
} /* readmap */


// --------------------------------------------------
// ------------------- INCLUSIONS -------------------
// --------------------------------------------------

void ReduceFullDimCubes (cubes Xcubes [], cubes Acubes [], int n)
// Reduce the full-dimensional sets of cubes in such a way that
// no information is lost if one is interested in computing the homomorphisms
// induced in homology by the inclusion maps between the subsequent sets.
// Note: The sets are modified such that they form an ascending sequence.
{
	// prepare a common variable for iterations (needed by MSVC++)
	register int i;

	// make sure that the sequence of the sets is ascending
	// and that the sets X and A are disjoint
	for (i = 1; i < n; i ++)
	{
		Xcubes [i]. add (Xcubes [i - 1]);
		Acubes [i]. add (Acubes [i - 1]);
		Xcubes [i]. remove (Acubes [i]);
	}

	// determine the dimension of the space
	int dim = -1;
	for (i = 1; i < n; i ++)
	{
		if (dim < 0)
		{
			if (!Acubes [i]. empty ())
				dim = Acubes [i] [0]. dim ();
			else if (!Xcubes [i]. empty ())
				dim = Xcubes [i] [0]. dim ();
		}
	}

	// throw an error message if all the sets are empty
	if (dim < 0)
		throw "All the sets are empty.";

	// allocate bitfields and display an appropriate message
	knownbits [dim];

	// reduce the sets of cubes
	for (i = 0; i < n; i ++)
	{
		// say what you are going to do
		sout << "Reducing full-dim cubes from ";
		if (!Acubes [i]. empty ())
			sout << "(X" << (i + 1) << ",A" << (i + 1) <<
				")... ";
		else
			sout << "X" << (i + 1) << "... ";

		// prepare the set which cannot be reduced (if relevant)
		cubes previousXA;
		cubes *prev = &previousXA;
		if (i && Acubes [i - 1]. empty ())
			prev = Xcubes + i - 1;
		else if (i && Xcubes [i - 1]. empty ())
			prev = Acubes + i - 1;
		else if (i)
		{
			previousXA. add (Xcubes [i - 1]);
			previousXA. add (Acubes [i - 1]);
		}

		// reduce the set or the pair of sets
		int_t count = cubreduce (Xcubes [i], Acubes [i], *prev);

		// say how well you did
		sout << count << " removed, " <<
			(Xcubes [i]. size () + Acubes [i]. size ()) <<
			" left.\n";
	}
	return;
} /* ReduceFullDimCubes */

void InclusionMapsHomology (cubes Xcubes [], cubes Acubes [],
	int n, chaincomplex<integer> **&homology,
	chainmap<integer> **&inclusions,
	multitable<cubicalcomplex> generators [])
// Compute the homomorphisms induced in homology by the inclusion maps
// of the pairs of sets (X [i], A [i]) into (X [i + 1], A [i + 1]).
// Allocate tables of chain complexes representing the homology of each
// set or pair of sets and allocate maps induced in homology between them.
// Store the generators of each pair into the corresponding table
// of cubical complexes.
{
	// if there are no maps to process, do nothing
	if (n <= 1)
		return;

	// prepare common variables for iterations (required by MSVC++)
	int i;
	int k;

	// determine the dimension of the space
	int dim = -1;
	for (i = 0; i < n; i ++)
	{
		if (!Xcubes [i]. empty ())
		{
			dim = Xcubes [i] [0]. dim ();
			break;
		}
	}
	if (dim < 0)
	{
		sout << "All the sets X are empty. "
			"The inclusions are trivial.\n";
		return;
	}

	// prepare a set of cubical cells that cannot be removed
	cubicalcomplex fixedcompl;

	// prepare a temporary variable for various local counts
	int_t count;

	// prepare the data for algebraic computations
	cubicalcomplex *Xcompl = new cubicalcomplex [n];
	cubicalcomplex *Acompl = new cubicalcomplex [n];
	chaincomplex<integer> **cx = new chaincomplex<integer> * [n];
	chaincomplex<integer> **cgraph = new chaincomplex<integer> * [n - 1];
	chainmap<integer> **cxproj = new chainmap<integer> * [n - 1];
	chainmap<integer> **cyproj = new chainmap<integer> * [n - 1];
	if (!cx || !cgraph || !cxproj || !cyproj)
		throw "Not enough memory for the inclusions.";

	// prepare the domain of the first inclusion map
	{
		int k = 0;
		sout << "\n*** Preparing the first set ***\n\n";

		// transform the set(s) of cubes into set(s) of cubical cells
		cubes2cells (Xcubes [k], Xcompl [k],
			Acubes [k]. empty () ? "X" : "X\\A", false);
		cubes2cells (Acubes [k], Acompl [k], "A", false);

		// reduce the pair of sets (Xcompl, Acompl) while adding
		// to them boundaries of all the cells
		sout << "Collapsing faces in " <<
			(Acompl [k]. empty () ? "X" : "X and A") << "... ";
		cubicalcomplex emptycompl;
		count = Xcompl [k]. collapse (Acompl [k], emptycompl,
			true, true, false);
		sout << 2 * count << " removed, " <<
			(Xcompl [k]. size () + Acompl [k]. size ()) <<
			" left.\n";

		// create the chain complex of the set or of the pair
		cx [k] = new chaincomplex<integer> (dim, true);
		sout << "Creating the chain complex of X... ";
		createchaincomplex (*(cx [k]), Xcompl [k], Acompl [k]);
		sout << "Done.\n";
	}

	// process all the inclusion maps
	for (k = 0; k < n - 1; k ++)
	{
		// show which inclusion is being processed
		sout << "\n*** Processing inclusion no. " << (k + 1) <<
			" ***\n\n";

		// transform the set(s) of cubes into set(s) of cubical cells
		cubes2cells (Xcubes [k + 1], Xcompl [k + 1],
			Acubes [k + 1]. empty () ? "X" : "X\\A", false);
		cubes2cells (Acubes [k + 1], Acompl [k + 1], "A", false);

		// create multivalued cubical maps for the inclusion
		sout << "Creating the multivalued cubical inclusion map... ";
		cubicalmap Fcubmap, FcubmapA;
		for (int_t i = 0; i < Xcubes [k]. size (); i ++)
		{
			Fcubmap [Xcubes [k] [i]].
				add (Xcubes [k] [i]);
		}
		for (int_t j = 0; j < Acubes [k]. size (); j ++)
		{
			FcubmapA [Acubes [k] [j]].
				add (Acubes [k] [j]);
		}
		sout << "Done.\n";

		// create the map F defined on the cells in A
		mvcellmap<qcell,integer,cube> FcellcubmapA (Acompl [k]);
		if (!Acompl [k]. empty ())
		{
			sout << "Creating the map F on cells in A... ";
			int_t count = createimages (FcellcubmapA, FcubmapA);
			sout << count << " cubes added.\n";
		}

		// create the map F defined on the cells in its domain
		mvcellmap<qcell,integer,cube> Fcellcubmap (Xcompl [k]);
		if (!Xcompl [k]. empty ())
		{
			sout << "Creating the map F on cells in X... ";
			int_t count = createimages (Fcellcubmap, Fcubmap,
				FcubmapA);
			sout << count << " cubes added.\n";
		}

		// create a reduced cell map for the inclusion
		sout << "Creating a cell map for F... ";
		mvcellmap<qcell,integer,qcell> Fcellmap (Xcompl [k]);
		createcellmap (Fcellcubmap, FcellcubmapA, Fcellmap, false);
		sout << "Done.\n";

		// convert the cell map into a graph
		cubicalcomplex Fcompl;
		sout << "Creating the graph of F... ";
		creategraph (Fcellmap, Fcompl, false);
		sout << Fcompl. size () << " cells added.\n";

		// create the chain complex of the graph of the map
		cgraph [k] = new chaincomplex<integer> (dim, false);
		sout << "Creating the chain complex of the graph of F" <<
			(k + 1) << "... ";
		createchaincomplex (*(cgraph [k]), Fcompl);
		sout << "Done.\n";

		// collapse the codomain of the map towards the image of F
		sout << "Taking the image of F and inclusion... ";
		cubicalcomplex emptycompl;
		int_t prev = fixedcompl. size ();
		project (Fcompl, fixedcompl, emptycompl, dim, dim, 0,
			NULL, false);
		sout << (fixedcompl. size () - prev) << " + ";
		prev = fixedcompl. size ();
		project (Fcompl, fixedcompl, emptycompl, 0, dim, dim,
			NULL, false);
		sout << (fixedcompl. size () - prev) << " cells added.\n";

		// add boundaries to and collapse the codomain of the map
		sout << "Collapsing Y towards F(X)... ";
		count = Xcompl [k + 1]. collapse (Acompl [k + 1], fixedcompl,
			true, true, false);
		sout << 2 * count << " cells removed, " <<
			Xcompl [k + 1]. size () << " left.\n";

		// create the chain complex of the codomain of the map
		cx [k + 1] = new chaincomplex<integer> (dim, true);
		sout << "Creating the chain complex of X" << (k + 2) <<
			"... ";
		createchaincomplex (*(cx [k + 1]), Xcompl [k + 1],
			Acompl [k + 1]);
		sout << "Done.\n";

		// create the projection map from the graph to X
		cxproj [k] = new chainmap<integer> (*(cgraph [k]),
			*(cx [k]));
		sout << "Creating the chain map of the projection to X... ";
		createprojection (Fcompl, Xcompl [k], *(cxproj [k]),
			0, dim, dim, NULL);
		sout << "Done.\n";

		// create the projection map from the graph to Y
		cyproj [k] = new chainmap<integer> (*(cgraph [k]),
			*(cx [k + 1]));
		sout << "Creating the chain map of the projection to Y... ";
		createprojection (Fcompl, Xcompl [k + 1], *(cyproj [k]),
			dim, dim, 0, NULL);
		sout << "Done.\n";
	}

	// prepare chains for keeping the results of homology computation
	chain<integer> **homx = new chain<integer> * [n];
	chain<integer> **homgraph = new chain<integer> * [n - 1];

	// indicate the computation progess
	sout << "\n*** Computing homology ***\n\n";
	for (i = 0; i < n; i ++)
		scon << '.';
	for (i = 0; i < n; i ++)
		scon << '\b';

	// compute the homology of the chain complexes corresponding to X
	for (k = 0; k < n; k ++)
	{
		cx [k] -> simple_form ((int *) NULL, true);
		cx [k] -> simple_homology (homx [k]);
		sout << '+';
	}

	// prepare a new progress indicator
	scon << "\b!\b";
	for (i = 0; i < n - 1; i ++)
		scon << "\b-\b";

	// compute the homology of the chain complexes of the graphs
	for (k = 0; k < n - 1; k ++)
	{
		sout << '*';
		cgraph [k] -> simple_form ((int *) NULL, true);
		cgraph [k] -> simple_homology (homgraph [k]);
	}
	sout << " Done.\n";

	// prepare the data structures for the homology
	chaincomplex<integer> **hx = new chaincomplex<integer> * [n];
	chaincomplex<integer> **hgraph = new chaincomplex<integer> * [n - 1];
	chainmap<integer> **hxproj = new chainmap<integer> * [n - 1];
	chainmap<integer> **hyproj = new chainmap<integer> * [n - 1];
	chainmap<integer> **hinclusion = new chainmap<integer> * [n - 1];

	// extract the algebraic form of homology
	for (k = 0; k < n; k ++)
	{
		hx [k] = new chaincomplex<integer> (dim);
		hx [k] -> take_homology (homx [k]);
	}
	for (k = 0; k < n - 1; k ++)
	{
		// retrieve the homology of the graph
		hgraph [k] = new chaincomplex<integer> (dim);
		hgraph [k] -> take_homology (homgraph [k]);
		// compute the inverse of homom. induced by the proj. onto X
		hxproj [k] = new chainmap<integer> (*(hgraph [k]),
			*(hx [k]));
		hxproj [k] -> take_homology (*(cxproj [k]),
			homgraph [k], homx [k]);
		hxproj [k] -> invert ();
		// compute the homomorphism induced by the projection onto Y
		hyproj [k] = new chainmap<integer> (*(hgraph [k]),
			*(hx [k + 1]));
		hyproj [k] -> take_homology (*(cyproj [k]),
			homgraph [k], homx [k + 1]);
		// compute the actual map as a composition of the other two
		hinclusion [k] = new chainmap<integer> (*(hx [k]),
			*(hx [k + 1]));
		hinclusion [k] -> compose (*(hyproj [k]), *(hxproj [k]));
	}

	// extract homology generators
	for (k = 0; k < n; k ++)
	{
		// set the generator counter to zero for each cubical set
		int_t current = 0;
		for (int d = 0; d <= cx [k] -> dim (); d ++)
		{
			// if there are no homology generators, skip this dim
			if (homx [k] [d]. empty ())
				continue;

			// retrieve the actual set of cubical cells
			const hashedset<qcell> &cset = Xcompl [k] [d];

			// add generators of this dimension to the result
			for (int_t i = 0; i < homx [k] [d]. size (); i ++)
			{
				// get the list of cells in this generator
				const chain<integer> &lst = cx [k] ->
					gethomgen (d, homx [k] [d]. num (i));

				// add all these cells to the resulting set
				for (int_t j = 0; j < lst. size (); j ++)
					generators [k] [current].
						add (cset [lst. num (j)]);

				// move to the next position in the list
				current ++;
			}
		}
	}

	// release memory and fill in the remaining part of the returned data
	delete [] Xcompl;
	delete [] Acompl;
	for (k = 0; k < n; k ++)
	{
		delete cx [k];
		if (homx [k])
			delete [] homx [k]; // MZ reported errors here; now OK
		// delete hx [k];
	}
	for (k = 0; k < n - 1; k ++)
	{
		delete cgraph [k];
		delete cxproj [k];
		delete cyproj [k];
		if (homgraph [k])
			delete [] homgraph [k]; // MZ reported errors here; now OK
		delete hgraph [k];
		delete hxproj [k];
		delete hyproj [k];
		// delete hinclusion [k];
	}
	delete [] cx;
	delete [] cgraph;
	delete [] cxproj;
	delete [] cyproj;
	delete [] homx;
	delete [] homgraph;
	// delete [] hx;
	delete [] hgraph;
	delete [] hxproj;
	delete [] hyproj;
	// delete [] hinclusion;

	homology = hx;
	inclusions = hinclusion;

	return;
} /* InclusionMapsHomology */

/// @}

