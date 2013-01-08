/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file homology/homology.h
///
/// This file contains various procedures for the homology computation.
/// This is - to certain extent - a "high-level" interface to the homology
/// library. These functions can be run to compute the homology of cubical
/// sets and maps, and the Betti numbers or torsion coefficients can be
/// extracted from the result in a convenient way.
///
/// It is worth to know that in this interface, the homology module
/// is encoded as an array of chains.
/// Each chain contains the information on homology for one level, beginning
/// with 0. Each entry of the chain contains either a unit (an invertible
/// coefficient, whose "delta" function equals 1) or the corresponding
/// torsion coefficient. By counting the number of invertible coefficients
/// one can determine the corresponding Betti number. The functions
/// "BettiNumber" and "TorsionCoefficient" can be used to extract these
/// quantities in a convenient way, without processing the chains themselves.
///
/// During the computations, various messages are written to the stream "sout"
/// and computation progress indicators are directed to "scon".
/// Use "sout. show = false" and "scon. show = false" to suppress
/// these messages.
/// Please, consult the details of the class "outputstream"
/// in "chomp/system/textfile.h" for more options,
/// including logging these messages to files.
///
/// In case of a fatal error, all the procedures throw a text (of the type
/// "char *" or "const char *") with the error message.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on August 14, 2003. Last revision: October 22, 2008.


#ifndef _CAPD_HOMOLOGY_HOMOLOGY_H_ 
#define _CAPD_HOMOLOGY_HOMOLOGY_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/timeused.h"
#include "capd/homology/arg.h"
#include "capd/homology/words.h"
#include "capd/homology/localvar.h"
#include "capd/homology/homtools.h"
#include "capd/homology/bincube.h"
#include "capd/homology/twolayer.h"

namespace capd {

/// This namespace contains the core of the homology computation
/// procedures and related classes and templates contained in the
/// CHomP C++ library.
namespace homology {


/// A class for representing a chain complex with integral coefficients.
typedef chaincomplex<integer> ChainComplex;

/// A class for representing a chain map with integral coefficients.
typedef chainmap<integer> ChainMap;

/// A class for representing a chain with integral coefficients.
typedef chain<integer> Chain;

/// A class for representing a set of simplices.
typedef hashedset<simplex> SetOfSimplices;

/// A class for representing a simplicial complex.
typedef gcomplex<simplex,integer> SimplicialComplex;


// --------------------------------------------------
// ------------ DECODE AND SHOW HOMOLOGY ------------
// --------------------------------------------------
// This is a set of procedures which help interprete
// the various form of homology encoding.

/// Returns the Betti number that corresponds to the given chain
/// which describes one homology group.
template <class euclidom>
int BettiNumber (const chain<euclidom> &c)
{
	int betti = 0;
	for (int i = 0; i < c. size (); ++ i)
	{
		if (c. coef (i). delta () == 1)
			++ betti;
	}
	return betti;
} /* BettiNumber */

/// Returns the next position in the chain containing a torsion coefficient.
/// Starts the search at the given position. Returns -1 if not found or the
/// position 'p' of the coefficient. This coefficient can be retrieved
/// as "c. coef (p)".
template <class euclidom>
int TorsionCoefficient (const chain<euclidom> &c, int start = 0)
{
	if (start < 0)
		return -1;
	while (start < c. size ())
	{
		if (c. coef (start). delta () != 1)
			return start;
		else
			++ start;
	}
	return -1;
} /* TorsionCoefficient */

/// Shows (that is, writes to 'sout') one level of the homology module
/// encoded in the given chain.
template <class euclidom>
inline void ShowHomology (const chain<euclidom> &c)
{
	int countfree = 0;
	bool writeplus = false;

	// write the homology module exactly in the order it appears in 'c'
	for (int i = 0; i < c. size (); ++ i)
	{
		// if the coefficient is invertible, it will be shown later
		if (c. coef (i). delta () == 1)
			++ countfree;
		// otherwise show the corresponding torsion part now
		else
		{
			sout << (writeplus ? " + " : "") <<
				euclidom::ringsymbol () << "_" <<
				c. coef (i);
			writeplus = true;
		}

		// if there were some free ingredients show them if necessary
		if (countfree && ((i == c. size () - 1) ||
			(c. coef (i + 1). delta () != 1)))
		{
			sout << (writeplus ? " + " : "") <<
				euclidom::ringsymbol ();
			if (countfree > 1)
				sout << "^" << countfree;
			countfree = 0;
			writeplus = true;
		}
	}

	// if there was nothing to show, then just show zero
	if (!c. size ())
		sout << "0";

	return;
} /* ShowHomology */

/// Shows (that is, writes to 'sout') the entire homology module
/// encoded in an array of chains.
template <class euclidom>
void ShowHomology (const chain<euclidom> *hom, int maxlevel)
{
	if (!hom)
		return;

	for (int q = 0; q <= maxlevel; ++ q)
	{
		sout << "H_" << q << " = ";
		ShowHomology (hom [q]);
		sout << '\n';
	}
	return;
} /* ShowHomology */

/// Show (that is, writes to 'sout') the homology map encoded in terms
/// of a chain map.
template <class euclidom>
inline void ShowHomology (const chainmap<euclidom> &hmap)
{
	hmap. show (sout, "\tf", "x", "y");
	return;
} /* ShowHomology */

/// Shows (that is, writes to 'sout') one generator of the homology module
/// of a chain complex. The generator is encoded in the given chain.
/// Note: The numbers of generators of the original chain complex are
/// displayed increased by 1 (that is, the first generator is "1", not "0").
template <class euclidom>
inline void ShowGenerator (const chain<euclidom> &c)
{
	c. show (sout, "c");
	return;
} /* ShowGenerator */

/// Shows (that is, writes to 'sout') all the generators of one level
/// of the homology module of a chain complex. Each generator is encoded
/// in one chain in the given array.
template <class euclidom>
void ShowGenerators (const chain<euclidom> *c, int count)
{
	for (int i = 0; i < count; ++ i)
	{
		sout << 'g' << (i + 1) << " = ";
		ShowGenerator (c [i]);
		sout << '\n';
	}
	return;
} /* ShowGenerators */

/// Shows (that is, writes to 'sout') all the generators of the entire
/// homology module of a chain complex.
/// Each level of generators is encoded in one array of chains.
template <class euclidom>
void ShowGenerators (chain<euclidom> const * const * const gen,
	const chain<euclidom> *hom, int maxlevel)
{
	for (int q = 0; q <= maxlevel; ++ q)
	{
		if (!hom [q]. size ())
			continue;
		sout << "[H_" << q << "]\n";
		ShowGenerators (gen [q], hom [q]. size ());
		sout << '\n';
	}
	return;
} /* ShowGenerators */

/// Shows (that is, writes to 'sout') all the generators of the entire
/// homology module of a chain complex.
/// The generators are retrieved from the chain complex itself.
template <class euclidom>
void ShowGenerators (const chaincomplex<euclidom> &c,
	const chain<euclidom> *hom, int maxlevel)
{
	for (int q = 0; q <= maxlevel; ++ q)
	{
		if (!hom [q]. size ())
			continue;
		sout << "[H_" << q << "]\n";
		for (int i = 0; i < hom [q]. size (); ++ i)
		{
			ShowGenerator (c. gethomgen (q, hom [q]. num (i)));
			sout << '\n';
		}
		sout << '\n';
	}
	return;
} /* ShowGenerators */

/// Shows (that is, writes to 'sout') one generator of the homology module
/// of a geometric complex. The generator is encoded in the given chain.
template <class cell,class euclidom>
void ShowGenerator (const chain<euclidom> &c, const hashedset<cell> &s)
{
	if (!c. size ())
		sout << '0';
	for (int i = 0; i < c. size (); ++ i)
	{
		euclidom e = c. coef (i);
		if (e == 1)
			sout << (i ? " + " : "") << s [c. num (i)];
		else if (-e == 1)
			sout << (i ? " - " : "-") << s [c. num (i)];
		else
		{
			sout << (i ? " + " : "") << e << " * " <<
				s [c. num (i)];
		}
	}
	return;
} /* ShowGenerator */

/// Shows (that is, writes to 'sout') all the generators of one level
/// of the homology module of a geometric complex. Each generator
/// is encoded in one chain in the given array.
template <class cell,class euclidom>
void ShowGenerators (const chain<euclidom> *c, int count,
	const hashedset<cell> &s)
{
	for (int i = 0; i < count; ++ i)
	{
		sout << 'g' << (i + 1) << " = ";
		ShowGenerator (c [i], s);
		sout << '\n';
	}
	return;
} /* ShowGenerators */

/// Shows all the generators of the entire homology module of a geometric
/// complex. Each level of generators is encoded in one array of chains.
template <class euclidom,class cell>
void ShowGenerators (chain<euclidom> * const *gen,
	const chain<euclidom> *hom,
	int maxlevel, const gcomplex<cell,euclidom> &gcompl)
{
	for (int q = 0; q <= maxlevel; ++ q)
	{
		if (!hom [q]. size ())
			continue;
		sout << "[H_" << q << "]\n";
		ShowGenerators (gen [q], hom [q]. size (), gcompl [q]);
		sout << '\n';
	}
	return;
} /* ShowGenerators */


// --------------------------------------------------
// ---------------- HOMOLOGY OF SETS ----------------
// --------------------------------------------------
// This is a set of procedures for the homology computation
// of various sets: chain complexes, geometric complexes
// (including cubical and simplicial complexes) and sets of cubes.

/// Extracts homology generators from a chain complex in the simple form.
/// Returns a pointer to an allocated table of tables of chains each of which
/// defines one generator of the homology module at the specified level.
/// Returns the zero pointer in case of error or if the homology is trivial.
template <class euclidom>
chain<euclidom> **ExtractGenerators (const chaincomplex<euclidom> &cx,
	chain<euclidom> *hom, int maxlevel)
// For instance: Chain **ExtractGenerators (const ChainComplex cx,
//	Chain *hom, int maxlevel).
{
	// if the maximal level is negative, then there is nothing to do
	if (maxlevel < 0)
		return 0;

	// create a table of tables of chains
	chain<euclidom> **gen = new chain<euclidom> * [maxlevel + 1];

	// extract generators for each homology level separately
	for (int q = 0; q <= maxlevel; ++ q)
	{
		// create a table of chains to hold the generators
		gen [q] = (hom [q]. size ()) ?
			new chain<euclidom> [hom [q]. size ()] : 0;

		// copy the corresponding chain from internal data of 'cx'
		for (int i = 0; i < hom [q]. size (); ++ i)
		{
			gen [q] [i] =
				cx. gethomgen (q, hom [q]. num (i));
		}
	}

	return gen;
} /* ExtractGenerators */

/// Transforms the chain complex into a simple form and compute its homology.
/// The changes of bases are reflected in all the chain maps
/// whose domain or codomain this chain complex is.
/// If the generators of the chain complex are to be retrieved,
/// the input chain complex must be created with a suitable option,
/// and the function ExtractGenerators can be used to extract them.
/// The table 'hom' is allocated or set to 0 in case of trivial homology.
/// Returns the number of the highest nontrivial homology level
/// or -1 if none.
template <class euclidom>
int Homology (chaincomplex<euclidom> &cx, const char *Xname,
	chain<euclidom> *&hom)
// For instance: int Homology (ChainComplex &cx, const char *Xname,
//	Chain *&hom).
{
	// initialize the empty table
	hom = 0;

	// determine the dimension of the chain complex
	int Xdim = cx. dim ();
	if (Xdim < 0)
		return -1;

	// compute the homology of the chain complex of X
	sout << "Computing the homology of " << Xname << " over " <<
		euclidom::ringname () << "...\n";
	cx. simple_form ((int *) 0, false);
	cx. simple_homology (hom);

	// determine the highest non-trivial homology level
	int maxlevel = Xdim;
	while ((maxlevel >= 0) && (hom [maxlevel]. size () <= 0))
		-- maxlevel;

	// if the homology is trivial, delete the allocated table (if any)
	if (hom && (maxlevel < 0))
	{
		delete [] hom;
		hom = 0;
	}

	return maxlevel;
} /* Homology */

/// Computes the homology of a given cubical complex. All the boundary cells
/// must be present (use the function for pairs with an empty set A
/// or "X. addboundaries ()" to add boundaries if necessary), because
/// missing cells give rise to missing generators of the corresponding
/// chain complex which indicates a relative cubical complex.
/// Destroy the contents of X before running the algebraic computations.
/// If 'gen' is given, the contents of X is not destroyed, and *gen is set
/// to point to a newly allocated table of tables of chains each of which
/// defines one generator of the homology module at a specified level.
/// Returns the number of the highest nontrivial homology level
/// or -1 if none.
template <class cell, class euclidom>
int Homology (gcomplex<cell,euclidom> &Xcompl, const char *Xname,
	chain<euclidom> *&hom, chain<euclidom> ***gen = 0)
// For instance: Homology (CubicalComplex &Xcompl, const char *Xname,
//	Chain *&hom, Chain ***gen = 0).
{
	// initialize the empty table
	hom = 0;

	// determine the dimension of the cubical complex
	int Xdim = Xcompl. dim ();
	if (Xdim < 0)
		return -1;

	// create a chain complex from the cubical complex X without adding
	// boundaries, as this might be a relative complex with A removed
	chaincomplex<euclidom> cx (Xdim, !!gen);
	sout << "Creating the chain complex of " << Xname << "... ";
	createchaincomplex (cx, Xcompl);
	sout << "Done.\n";

	// forget the geometric cubical complex to release memory
	if (!gen)
	{
		gcomplex<cell,euclidom> empty;
		Xcompl = empty;
	}

	// compute the homology of this chain complex
	int maxlevel = Homology (cx, Xname, hom);

	// extract the generators of homology ('cx' will be lost on 'return')
	if (gen)
		*gen = ExtractGenerators (cx, hom, maxlevel);

	return maxlevel;
} /* Homology */

/// Computes the homology of a given set of cubes. The set is destroyed.
/// If the generators are to be retrieved, the table 'gen' is allocated as in
/// the Homology function for geometric complexes, and the pointer pointed to
/// by 'gcompl' is set to the cubical complex arising in the computations.
/// Returns the number of the highest nontrivial homology level
/// or -1 if none.
template <class euclidom, class cubetype>
int Homology (hashedset<cubetype> &Xcubes, const char *Xname,
	chain<euclidom> *&hom, chain<euclidom> ***gen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gcompl = 0)
// For instance: Homology (SetOfCubes &Xcubes, const char *Xname,
//	Chain *&hom, Chain ***gen = 0, CubicalComplex **gcompl = 0).
{
	// define the type of a set of cubes
	typedef hashedset<cubetype> cubsettype;

	// define the type of a cubical cell
	typedef typename cubetype::CellType celltype;

	// initialize the empty table
	hom = 0;

	// if the set X is empty, the answer is obvious
	if (Xcubes. empty ())
		return -1;

	// determine the dimension of X (note: X is nonempty!)
	int Xspacedim = Xcubes [0]. dim ();

	// allocate a suitable bit field set for the reduction and show msg
	knownbits [Xspacedim];

	// reduce the cubes in X
	cubsettype emptycubes;
	reducepair (Xcubes, emptycubes, emptycubes, Xname, 0);

	// transform the set of cubes X into a set of cells and forget Xcubes
	gcomplex<celltype,euclidom> *Xcompl =
		new gcomplex<celltype,euclidom>;
	cubes2cells (Xcubes, *Xcompl, Xname);
	Xcubes = emptycubes;

	// collapse the set and add boundaries of cells
	collapse (*Xcompl, Xname);

	// if the complex is empty, the result is trivial
	if (Xcompl -> empty ())
	{
		delete Xcompl;
		return -1;
	}

	// make a correction to the dimension of X
	int Xdim = Xcompl -> dim ();
	if (Xdim != Xspacedim)
	{
		sout << "Note: The dimension of " << Xname <<
			" decreased from " << Xspacedim <<
			" to " << Xdim << ".\n";
	}

	// compute the homology of the cubical complex
	int maxlevel = Homology (*Xcompl, Xname, hom, gen);

	// deallocate the cubical complex if necessary
	if (!gcompl)
		delete Xcompl;
	else
		*gcompl = Xcompl;

	return maxlevel;
} /* Homology */

/// Computes the relative homology of the given pair of cubical complexes.
/// Begins with adding boundaries to the cells in A and in X while removing
/// from X all the cells that appear in A to make X a relative cell complex.
/// Destroys the contents of X and A before running the algebraic
/// computations unless homology generators are to be retrieved.
/// Note that if A is empty then all possible boundaries will be added to X.
/// Returns the number of the highest nontrivial homology level
/// or -1 if none.
template <class cell, class euclidom>
int Homology (gcomplex<cell,euclidom> &Xcompl, const char *Xname,
	gcomplex<cell,euclidom> &Acompl, const char *Aname,
	chain<euclidom> *&hom, chain<euclidom> ***gen = 0)
// For instance: Homology (CubicalComplex &Xcompl, const char *Xname,
//	CubicalComplex &Acompl, const char *Aname, Chain *&hom,
//	Chain ***gen = 0).
{
	// initialize the empty table
	hom = 0;

	// determine the dimension of the first cubical complex
	int Xdim = Xcompl. dim ();
	if (Xdim < 0)
		return -1;

	// prepare the right name for the pair (to be used later)
	word pairname;
	if (!Acompl. empty ())
		pairname << '(' << Xname << "," << Aname << ')';
	else
		pairname << Xname;

	// collapse the pair of sets into a relative cubical complex
	// and add boundaries of cells where necessary
	collapse (Xcompl, Acompl, Xname, Aname);

	// forget the remains of the other cubical complex
	gcomplex<cell,euclidom> emptycompl;
	Acompl = emptycompl;

	// make a correction to the dimension of X
	if (Xdim != Xcompl. dim ())
	{
		sout << "Note: The dimension of " << Xname <<
			" decreased from " << Xdim << " to " <<
			Xcompl. dim () << ".\n";
	}

	// compute the homology of the relative cubical complex
	int maxlevel = Homology (Xcompl, pairname, hom, gen);

	// release memory used by the name of the pair and exit
	return maxlevel;
} /* Homology */

/// Computes the relative homology of a given pair of sets of cubes.
/// Modifies the sets and then destroy them during the computations.
/// If homology generators are to be retrieved, no expansion of A in X is
/// performed.
/// If the generators are to be retrieved, the table 'gen' is allocated as in
/// the Homology function for geometric complexes, and the pointer pointed to
/// by 'gcompl' is set to the cubical complex arising in the computations.
/// Returns the number of the highest nontrivial homology level
/// or -1 if none.
template <class euclidom, class cubetype>
int Homology (hashedset<cubetype> &Xcubes, const char *Xname,
	hashedset<cubetype> &Acubes, const char *Aname,
	chain<euclidom> *&hom, chain<euclidom> ***gen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gcompl = 0)
// For instance: int Homology (SetOfCubes &X, const char *Xname,
//	SetOfCubes &A, const char *Aname, Chain *&hom,
//	Chain ***gen = 0, CubicalComplex **gcompl = 0).
{
	// define the type of a set of cubes
	typedef hashedset<cubetype> cubsettype;

	// define the type of a cubical cell
	typedef typename cubetype::CellType celltype;

	// initialize the empty table
	hom = 0;

	// if the set A is empty, call the other procedure
	if (Acubes. empty ())
		return Homology (Xcubes, Xname, hom, gen, gcompl);

	// remove from X cubes which are in A
	removeAfromX (Xcubes, Acubes, Xname, Aname);

	// if the set X is empty, the answer is obvious
	if (Xcubes. empty ())
		return -1;

	// leave in A only the neighbors of X\\A
	restrictAtoneighbors (Xcubes, Acubes, Xname, Aname);

	// determine the dimension of X (note: X is nonempty!)
	int Xspacedim = Xcubes [0]. dim ();

	// allocate a suitable bit field set for the reduction and show msg
	knownbits [Xspacedim];

	// expand A within X
	if (!gcompl)
		expandAinX (Xcubes, Acubes, Xname, Aname);

	// if everything was moved to A, then the result is trivial
	if (Xcubes. empty ())
		return -1;

	// restrict A to neighbors
	restrictAtoneighbors (Xcubes, Acubes, Xname, Aname);

	// reduce the pair (X,A)
	cubsettype emptycubes;
	reducepair (Xcubes, Acubes, emptycubes, Xname, Aname);

	// if nothing remains in X, then the result is trivial
	if (Xcubes. empty ())
		return -1;

	// prepare the right name for the difference of the two sets
	word diffname;
	diffname << Xname << '\\' << Aname;

	// transform the set of cubes X into a set of cells and forget Xcubes
	gcomplex<celltype,euclidom> *Xcompl =
		new gcomplex<celltype,euclidom>;
	cubes2cells (Xcubes, *Xcompl, diffname);
	Xcubes = emptycubes;

	// transform the set of cubes A into a set of cubical cells
	gcomplex<celltype,euclidom> Acompl;
	cubes2cells (Acubes, Acompl, Aname);
	Acubes = emptycubes;

	// continue the homology computations
	int maxlevel = Homology (*Xcompl, Xname, Acompl, Aname, hom, gen);

	// deallocate the cubical complex if necessary
	if (!gcompl)
		delete Xcompl;
	else
		*gcompl = Xcompl;

	return maxlevel;
} /* Homology */


// --------------------------------------------------
// ---------------- HOMOLOGY OF MAPS ----------------
// --------------------------------------------------
// This is a set of procedures for the homology computation
// of chain maps and combinatorial cubical multivalued maps.

/// Extracts the homomorphism induced in homology from the chain map
/// on two chain complexes whose homology has just been computed.
/// Note that 'maxlevel' must be the MINIMUM of the two maximal
/// nontrivial homology levels encoded in "hom_cx" and "hom_cy".
/// Returns a pointer to the extracted homomorphism.
///
/// Explanation:
/// In order to compute the homomorphism induced in homology by a chain map,
/// it is enough to define the chain map between two chain complexes (one can
/// also use the same chain complex for its domain and codomain if the map is
/// an endomorphism), and then compute the homology of both chain complexes.
/// One can use one of the functions below to extract the information
/// obtained in this way into a simpler (and smaller) data structure.
/// The extracted map is exactly the homomorphism induced in homology.
/// Since the returned chain map is allocated with the 'new' operator,
/// one should 'delete' it when finished.
template <class euclidom>
chainmap<euclidom> *HomologyMap (const chainmap<euclidom> &cmap,
	const chain<euclidom> *hom_cx,
	const chain<euclidom> *hom_cy, int maxlevel)
// For instance: ChainMap *HomologyMap (const ChainMap &cmap,
//	const Chain *hom_cx, const Chain *hom_cy, int maxlevel).
{
	// if the maximal level is wrong, return 0
	if (maxlevel < 0)
		return 0;

	// allocate chain complexes of appropriate dimension and a chain map
	chaincomplex<euclidom> hx (maxlevel);
	chaincomplex<euclidom> hy (maxlevel);
	chainmap<euclidom> *hmap = new chainmap<euclidom> (hx, hy);

	// create the chain complexes reflecting the homology module(s)
	hx. take_homology (hom_cx);
	hy. take_homology (hom_cy);

	// create the chain map accordingly
	hmap -> take_homology (cmap, hom_cx, hom_cy);
	return hmap;
} /* HomologyMap */

/// Extracts the endomorphism induced in homology from the chain map
/// on one chain complex whose homology has just been computed.
/// Returns a pointer to the extracted homomorphism.
template <class euclidom>
chainmap<euclidom> *HomologyMap (const chainmap<euclidom> &cmap,
	const chain<euclidom> *hom_cx, int maxlevel)
// For instance: ChainMap *HomologyMap (const ChainMap &cmap,
//	const Chain *hom_cx, int maxlevel).
{
	// if the maximal level is wrong, return 0
	if (maxlevel < 0)
		return 0;

	// allocate chain complexes of appropriate dimension and a chain map
	chaincomplex<euclidom> hx (maxlevel);
	chainmap<euclidom> *hmap = new chainmap<euclidom> (hx, hx);

	// create the chain complexes reflecting the homology module(s)
	hx. take_homology (hom_cx);

	// create the chain map accordingly
	hmap -> take_homology (cmap, hom_cx, hom_cx);
	return hmap;
} /* HomologyMap */

/// Computes the homomorphism induced in homology by a combinatorial cubical
/// multivalued map. Deletes the contents of X, A, Y, B and F when used.
/// Fills in the given data with the computed result.
/// If 'inclusion' is true, then composes the result with the inverse
/// of the homomorphism induced in homology by the inclusion (X,A) -> (Y,B).
/// If the inclusion is not invertible, throws an error message.
/// Note that (X,A) and (Y,B) are modified independently, so you can't
/// just pass the same sets to this procedure; you must clone them first.
/// Set 'careful' bits: 0x01 = basic data verification, 0x02 = preserve
/// the map's acyclicity in reductions (this can be slow!).
/// Displays the computed homology and homomorphisms to the screen.
/// Returns the highest nontrivial homology level for the map or -1 if none.
template <class euclidom, class cubetype>
int Homology (mvmap<cubetype,cubetype> &Fcubmap, const char *Fname,
	hashedset<cubetype> &Xcubes, const char *Xname,
	hashedset<cubetype> &Acubes, const char *Aname,
	hashedset<cubetype> &Ycubes, const char *Yname,
	hashedset<cubetype> &Bcubes, const char *Bname,
	chain<euclidom> *&hom_cx, int &maxlevel_cx,
	chain<euclidom> *&hom_cy, int &maxlevel_cy,
	chainmap<euclidom> *&hom_f,
	bool inclusion = false, int careful = 0x01,
	chain<euclidom> ***gfgen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gfcompl = 0,
	chain<euclidom> ***gygen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gycompl = 0)
{
	// define the type of a set of cubes
	typedef hashedset<cubetype> cubsettype;

	// define the type of a cubical cell
	typedef typename cubetype::CellType celltype;

	// define the type of a combinatorial cubical multivalued map
	typedef mvmap<cubetype,cubetype> cubmaptype;

	// transform the 'careful' bits into separate variables
	bool verify = careful & 0x01;
	bool checkacyclic = careful & 0x02;

	// prepare the right names for X\A and Y\B
	word XAname, YBname;
	if (!Acubes. empty ())
		XAname << Xname << '\\' << Aname;
	else
		XAname << Xname;
	if (!Bcubes. empty ())
		YBname << Yname << '\\' << Bname;
	else
		YBname << Yname;

	// ----- prepare the sets of cubes -----

	// if the pointers to both sets are the same, then this is an error
	if (&Xcubes == &Ycubes)
		throw "You must clone the sets passed to Homology.";

	// remove from X cubes which are in A
	removeAfromX (Xcubes, Acubes, Xname, Aname);

	// leave in A only the neighbors of X\\A
	restrictAtoneighbors (Xcubes, Acubes, Xname, Aname);

	// remove from Y cubes which are in B
	removeAfromX (Ycubes, Bcubes, Yname, Bname);

	// if one of the main sets is empty, the answer is trivial
	if (Xcubes. empty () || Ycubes. empty ())
		return -1;

	// remember the original size of the set A and of the set X
	int_t origAsize = Acubes. size ();
	int_t origXsize = Xcubes. size ();

	// determine the dimension of X and Y (both sets are non-empty)
	int Xspacedim = Xcubes [0]. dim ();
	int Yspacedim = Ycubes [0]. dim ();

	// check if F (X\A) \subset Y
	if (verify)
		checkimagecontained (Fcubmap, Xcubes, Ycubes, Bcubes,
			XAname, Yname);

	// check if F (A) \subset B
	if (verify && !Acubes. empty ())
		checkimagecontained (Fcubmap, Acubes, Bcubes, Aname, Bname);

	// check if F (A) is disjoint from Y
	if (verify && !Acubes. empty ())
		checkimagedisjoint (Fcubmap, Acubes, Ycubes, Aname, YBname);

	// verify if X\A \subset Y and A \subset B if inclusion is considered
	if (verify && inclusion)
		checkinclusion (Xcubes, Ycubes, Bcubes, XAname, Yname);
	if (verify && inclusion)
		checkinclusion (Acubes, Bcubes, Aname, Bname);

	// ----- reduce the sets of cubes -----

	// allocate a suitable bit field set for the reduction and show msg
	knownbits [Xspacedim];
	knownbits [Yspacedim];

	// reduce the pair of sets of cubes (X,A) without acyclicity check
	if (!checkacyclic)
	{
		// reduce the pair (X,A)
		cubsettype empty;
		reducepair (Xcubes, Acubes, empty, Xname, Aname);

		// if nothing remains in X, then the result is trivial
		if (Xcubes. empty ())
			return -1;
	}

	// expand A towards X and modify (Y,B) accordingly
	if (!Acubes. empty () && !gfgen && !gygen)
	{
		expandAinX (Xcubes, Acubes, Ycubes, Bcubes, Fcubmap,
			Xname, Aname, Bname, inclusion, checkacyclic);
	}

	// reduce the pair (X,A) or the set X with acyclicity check
	if (checkacyclic && !Acubes. empty ())
	{
		// leave in A only the neighbors of X\\A
		restrictAtoneighbors (Xcubes, Acubes, Xname, Aname);

		// reduce the pair (X,A) with acyclicity check
		cubsettype emptycubes;
		reducepair (Xcubes, Acubes, Fcubmap, emptycubes,
			Xname, Aname);

		// if nothing remains in X, then the result is trivial
		if (Xcubes. empty ())
			return -1;
	}

	// reduce the pair (X,A) even further
	if (!checkacyclic && !Acubes. empty ())
	{
		// leave in A only the neighbors of X\\A
		restrictAtoneighbors (Xcubes, Acubes, Xname, Aname);

		// continue the reduction of the pair (X,A)
		cubsettype empty;
		reducepair (Xcubes, Acubes, empty, Xname, Aname);
	}

	// indicate that the acyclicity of the map should be verified
	if (!verify)
	{
		if (!checkacyclic && ((origAsize != Acubes. size ()) ||
			(origXsize != Xcubes. size ())))
		{
			sout << "*** Important note: " << Xname << " or " <<
				Aname << " changed. You must make sure\n"
				"*** that the restriction of " << Fname <<
				" to the new sets is acyclic.\n";
		}
		else
		{
			sout << "*** Note: The program assumes "
				"that the input map is acyclic.\n";
		}
	}

	// create the set of cubes to keep in Y as the image of the domain
	// and include the domain if the inclusion is considered
	cubsettype Ykeepcubes;
	sout << "Computing the image of the map... ";
	for (int_t i = 0; i < Xcubes. size (); ++ i)
		Ykeepcubes. add (Fcubmap (Xcubes [i]));
	for (int_t i = 0; i < Acubes. size (); ++ i)
		Ykeepcubes. add (Fcubmap (Acubes [i]));
	if (inclusion)
	{
		sout << "and of the inclusion... ";
		Ykeepcubes. add (Xcubes);
		Ykeepcubes. add (Acubes);
	}
	sout << Ykeepcubes. size () << " cubes.\n";

	// reduce the pair of cubical sets (Y,B) towards the image of F
	if (Xspacedim == Yspacedim)
	{
		if (!gygen)
			expandAinX (Ycubes, Bcubes, Yname, Bname);
		restrictAtoneighbors (Ycubes, Bcubes, Yname, Bname,
			&Ykeepcubes);
		reducepair (Ycubes, Bcubes, Ykeepcubes, Yname, Bname);
	}

	// forget the cubes to keep in Y as no longer of any use
	if (!Ykeepcubes. empty ())
	{
		cubsettype empty;
		Ykeepcubes = empty;
	}

	// ----- create the cubical complexes -----

	// transform the set of cubes X into a set of cells and forget Xcubes
	gcomplex<celltype,euclidom> Xcompl;
	cubes2cells (Xcubes, Xcompl, XAname, false);

	// transform the set of cubes A into a set of cubical cells
	gcomplex<celltype,euclidom> Acompl;
	cubes2cells (Acubes, Acompl, Aname, false);

	// transform the cubes in Y into cubical cells and forget the cubes
	gcomplex<celltype,euclidom> *Ycompl =
		new gcomplex<celltype,euclidom>;
	cubes2cells (Ycubes, *Ycompl, YBname);

	// transform the cubes in B into cubical cells and forget the cubes
	gcomplex<celltype,euclidom> Bcompl;
	cubes2cells (Bcubes, Bcompl, Bname);

	// determine the dimension of X and Y as cubical complexes
	int Xdim = Xcompl. dim ();
	int Ydim = Ycompl -> dim ();

	// ----- collapse the cubical sets (X,A) -----

	// reduce the pair of sets (Xcompl, Acompl) while adding to them
	// boundaries of all the cells
	gcomplex<celltype,euclidom> emptycompl;
	collapse (Xcompl, Acompl, emptycompl, Xname, Aname,
		true, true, false);

	// if nothing remains in X, then the result is trivial
	if (Xcompl. empty ())
		return -1;

	// make a correction to the dimension of X
	if (Xdim != Xcompl. dim ())
	{
		sout << "Note: The dimension of " << Xname << " decreased "
			"from " << Xdim << " to " << Xcompl. dim () << ".\n";

		Xdim = Xcompl. dim ();
	}

	// ----- create a reduced graph of F -----

	// create the map F defined on the cells in its domain
	mvcellmap<celltype,euclidom,cubetype> Fcellcubmap (Xcompl);
	sout << "Creating the map " << Fname << " on cells in " <<
		Xname << "... ";
	int_t countimages = createimages (Fcellcubmap, Fcubmap, Fcubmap,
		Xcubes, Acubes);
	sout << countimages << " cubes added.\n";

	// create the map F defined on the cells in its domain subcomplex A
	mvcellmap<celltype,euclidom,cubetype> FcellcubmapA (Acompl);
	if (!Acompl. empty ())
	{
		sout << "Creating the map " << Fname << " on cells in " <<
			Aname << "... ";
		int_t count = createimages (FcellcubmapA, Fcubmap, Acubes);
		sout << count << " cubes added.\n";
	}

	// get rid of the sets of cubes X and A as no longer needed,
	// as well as the cubical map
	{
		cubsettype emptycubes;
		Acubes = emptycubes;
		Xcubes = emptycubes;
		cubmaptype emptymap;
		Fcubmap = emptymap;
	}

	// create the graph of F as a cubical cell complex
	sout << "Creating a cell map for " << Fname << "... ";
	mvcellmap<celltype,euclidom,celltype> Fcellmap (Xcompl);
	bool acyclic = createcellmap (Fcellcubmap, FcellcubmapA,
		Fcellmap, verify);
	sout << "Done.\n";
	if (verify && !acyclic)
	{
		sout << "*** SERIOUS PROBLEM: The map is not "
			"acyclic. THE RESULT WILL BE WRONG.\n"
			"*** You must verify the acyclicity of the "
			"initial map with 'chkmvmap'\n"
			"*** and, if successful, set the "
			"'careful reduction' bit.\n";
	}
	if (verify && acyclic)
	{
		sout << "Note: It has been verified successfully "
			"that the map is acyclic.\n";
	}

	sout << "Creating the graph of " << Fname << "... ";
	gcomplex<celltype,euclidom> *Fcompl =
		new gcomplex<celltype,euclidom>;
	creategraph (Fcellmap, *Fcompl, false);
	sout << Fcompl -> size () << " cells added.\n";

	// forget the cubical maps on the cells and the cubical complex of X
	mvcellmap<celltype,euclidom,cubetype> emptycellcubmap;
	Fcellcubmap = emptycellcubmap;
	FcellcubmapA = emptycellcubmap;
	mvcellmap<celltype,euclidom,celltype> emptycellmap (emptycompl);
	Fcellmap = emptycellmap;
	Xcompl = emptycompl;

	// ----- collapse the cubical sets (Y,B) -----

	// decrease the dimension of B to the dimension of Y
	decreasedimension (Bcompl, Ydim, Bname);

	// create a full cubical complex (with all the faces) of Y\B
	addboundaries (*Ycompl, Bcompl, 0, false, Yname, Bname);

	// forget the cubical complex of B
	if (!Bcompl. empty ())
	{
		sout << "Forgetting " << Bcompl. size () << " cells from " <<
			Bname << ".\n";
		gcomplex<celltype,euclidom> empty;
		Bcompl = empty;
	}

	// collapse the codomain of the map towards the image of F
	gcomplex<celltype,euclidom> Ykeepcompl;
	sout << "Computing the image of " << Fname << "... ";
	project (*Fcompl, Ykeepcompl, *Ycompl, Xspacedim, Yspacedim,
		0, 0, false);
	if (inclusion)
	{
		project (*Fcompl, Ykeepcompl, *Ycompl, 0, Xspacedim,
			Yspacedim, 0, false);
	}
	sout << Ykeepcompl. size () << " cells.\n";

	sout << "Collapsing " << Yname << " to img of " << Xname << "... ";
	int_t countremoved = Ycompl -> collapse (emptycompl, Ykeepcompl,
		0, 0, 0);
	sout << 2 * countremoved << " cells removed, " <<
		Ycompl -> size () << " left.\n";

	// forget the cells to keep in Y
	if (!Ykeepcompl. empty ())
	{
		gcomplex<celltype,euclidom> empty;
		Ykeepcompl = empty;
	}

	// make a correction to the dimension of Y
	if (Ydim != Ycompl -> dim ())
	{
		sout << "Note: The dimension of " << Yname << " decreased "
			"from " << Ydim << " to " << Ycompl -> dim () <<
			".\n";

		Ydim = Ycompl -> dim ();
	}

	// ----- create chain complexes from the cubical sets ------

	// create a chain complex from the graph of F (it is relative)
	chaincomplex<euclidom> cgraph (Fcompl -> dim (), !!gfgen);
	sout << "Creating the chain complex of the graph of " << Fname <<
		"... ";
	createchaincomplex (cgraph, *Fcompl);
	sout << "Done.\n";

	// create the chain complex from Y (this is a relative complex)
	chaincomplex<euclidom> cy (Ydim, !!gygen);
	sout << "Creating the chain complex of " << Yname << "... ";
	createchaincomplex (cy, *Ycompl);
	sout << "Done.\n";

	// create the projection map from the graph of the map to Y
	chainmap<euclidom> cmap (cgraph, cy);
	sout << "Creating the chain map of the projection... ";
	createprojection (*Fcompl, *Ycompl, cmap, Xspacedim, Yspacedim, 0);
	sout << "Done.\n";

	// if this is an index map, create the projection map from the graph
	// of the map to X composed with the inclusion into Y
	chainmap<euclidom> imap (cgraph, cy);
	if (inclusion)
	{
		sout << "Creating the chain map of the inclusion... ";
		createprojection (*Fcompl, *Ycompl, imap, 0, Xspacedim,
			Yspacedim);
		sout << "Done.\n";
	}

	// forget the graph of F if it is not going to be used anymore
	if (gfcompl)
		(*gfcompl) = Fcompl;
	else
		delete Fcompl;

	// forget the cubical complex Y unless requested to keep it
	if (gycompl)
		(*gycompl) = Ycompl;
	else
		delete Ycompl;

	// ----- compute and show homology, save generators -----

	// prepare the name of the graph of F
	word gFname;
	gFname << "the graph of " << Fname;

	// compute the homology of the chain complex of the graph of the map
	maxlevel_cx = Homology (cgraph, gFname, hom_cx);

	// extract the computed generators of the graph if requested to
	if (gfgen)
		*gfgen = ExtractGenerators (cgraph, hom_cx, maxlevel_cx);

	// compute the homology of the chain complex of Y
	maxlevel_cy = Homology (cy, Yname, hom_cy);

	// extract the computed generators of Y if requested to
	if (gygen)
		*gygen = ExtractGenerators (cy, hom_cy, maxlevel_cy);

	// ----- show the map(s) -----

	// prepare the data structures for the homology
	chaincomplex<euclidom> hgraph (maxlevel_cx);
	chaincomplex<euclidom> hy (maxlevel_cy);
	chainmap<euclidom> *hmap = new chainmap<euclidom> (hgraph, hy);
	chainmap<euclidom> hincl (hgraph, hy);
//	chainmap<euclidom> *hcomp = new chainmap<euclidom> (hgraph, hgraph);
	chainmap<euclidom> *hcomp = new chainmap<euclidom> (hy, hy);

	// show the map induced in homology by the chain map
	sout << "The map induced in homology is as follows:\n";
	hgraph. take_homology (hom_cx);
	hy. take_homology (hom_cy);
	hmap -> take_homology (cmap, hom_cx, hom_cy);
	hmap -> show (sout, "\tf", "x", "y");

	// show the map induced in homology by the inclusion map
	bool invertible = true;
	if (inclusion)
	{
		sout << "The map induced in homology by the inclusion:\n";
		hincl. take_homology (imap, hom_cx, hom_cy);
		hincl. show (sout, "\ti", "x", "y");

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
			sout << "The inverse of the map "
				"induced by the inclusion:\n";
			hincl. show (sout, "\tI", "y", "x");

			// debug: verify if the map was inverted correctly
			chainmap<euclidom> hincl1 (hgraph, hy);
			hincl1. take_homology (imap, hom_cx, hom_cy);
			chainmap<euclidom> hident (hy, hy);
			hident. compose (hincl1, hincl);
			sbug << "The composition of the inclusion and "
				"its inverse (should be the identity):\n";
			hident. show (sbug, "\tid", "y", "y");
			for (int i = 0; i <= hident. dim (); ++ i)
			{
				const mmatrix<euclidom> &m = hident [i];
				if (m. getnrows () != m. getncols ())
					throw "INV: Inequal rows and cols.";
				euclidom zero, one;
				zero = 0;
				one = 1;
				for (int c = 0; c < m. getncols (); ++ c)
				{
					for (int r = 0; r < m. getnrows ();
						++ r)
					{
						if ((r == c) && (m. get
							(r, c) == one))
						{
							continue;
						}
						if (m. get (r, c) == zero)
							continue;
						throw "INV: Non-identity.";
					}
				}
			}
			// debug: end of the verification

			sout << "The composition of F and the inverse "
				"of the map induced by the inclusion:\n";
		//	hcomp -> compose (hincl, *hmap);
			hcomp -> compose (*hmap, hincl);
		//	hcomp -> show (sout, "\tF", "x", "x");
			hcomp -> show (sout, "\tF", "y", "y");
		}
	}

	// set the appropriate map
	if (inclusion && invertible)
	{
		hom_f = hcomp;
		delete hmap;
	}
	else
	{
		hom_f = hmap;
		delete hcomp;
	}

	// throw an exception if the map is not invertible
	if (inclusion && !invertible)
		throw "Unable to invert the inclusion map.";

	return ((maxlevel_cx < maxlevel_cy) ? maxlevel_cx : maxlevel_cy);
} /* Homology */

/// A version of the above procedure with the default names.
template <class euclidom, class cubetype>
int Homology (mvmap<cubetype,cubetype> &Fcubmap,
	hashedset<cubetype> &Xcubes, hashedset<cubetype> &Acubes,
	hashedset<cubetype> &Ycubes, hashedset<cubetype> &Bcubes,
	chain<euclidom> *&hom_cx, int &maxlevel_cx,
	chain<euclidom> *&hom_cy, int &maxlevel_cy,
	chainmap<euclidom> *&hom_f,
	bool inclusion = false, int careful = 0x01,
	chain<euclidom> ***gfgen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gfcompl = 0,
	chain<euclidom> ***gygen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gycompl = 0)
{
	return Homology (Fcubmap, "F", Xcubes, "X", Acubes, "A",
		Ycubes, "Y", Bcubes, "B", hom_cx, maxlevel_cx,
		hom_cy, maxlevel_cy, hom_f, inclusion, careful,
		gfgen, gfcompl, gygen, gycompl);
} /* Homology */

/// Computes the endomorphism induced in homology by a combinatorial cubical
/// multivalued map. See the description of the previous function
/// for details.
template <class euclidom, class cubetype>
int Homology (mvmap<cubetype,cubetype> &Fcubmap, const char *Fname,
	hashedset<cubetype> &Xcubes, const char *Xname,
	hashedset<cubetype> &Acubes, const char *Aname,
	chain<euclidom> *&hom, int &maxlevel,
	chainmap<euclidom> *&hom_f, int careful = 0x01,
	chain<euclidom> ***gfgen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gfcompl = 0,
	chain<euclidom> ***gygen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gycompl = 0)
{
	hashedset<cubetype> Ycubes = Xcubes, Bcubes = Acubes;
	chain<euclidom> *hom_cy = 0;
	int maxlevel_cy;
	int result = Homology (Fcubmap, Fname, Xcubes, Xname, Acubes, Aname,
		Ycubes, Xname, Bcubes, Aname, hom, maxlevel,
		hom_cy, maxlevel_cy, hom_f, true, careful,
		gfgen, gfcompl, gygen, gycompl);
	delete [] hom_cy;
	return result;
} /* Homology */

/// A version of the above procedure with the default names.
template <class euclidom, class cubetype>
int Homology (mvmap<cubetype,cubetype> &Fcubmap,
	hashedset<cubetype> &Xcubes, hashedset<cubetype> &Acubes,
	chain<euclidom> *&hom, int &maxlevel,
	chainmap<euclidom> *&hom_f, int careful = 0x01,
	chain<euclidom> ***gfgen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gfcompl = 0,
	chain<euclidom> ***gygen = 0,
	gcomplex<typename cubetype::CellType,euclidom> **gycompl = 0)
{
	return Homology (Fcubmap, "F", Xcubes, "X", Acubes, "A", hom,
		maxlevel, hom_f, careful, gfgen, gfcompl, gygen, gycompl);
} /* Homology */


// --------------------------------------------------
// --------- TWO-LAYER HOMOLOGY COMPUTATION ---------
// --------------------------------------------------

/// Computes the endomorphism induced in homology by a combinatorial
/// cubical multivalued map using the two-layer construction
/// developped by P. Pilarczyk and K. Stolot.
template <class euclidom, class cubetype>
int Homology2l (mvmap<cubetype,cubetype> &Fcubmap0, const char *Fname,
	hashedset<cubetype> &Xcubes0, const char *Xname,
	hashedset<cubetype> &Acubes0, const char *Aname,
	chain<euclidom> *&hom_cx, int &maxlevel,
	chainmap<euclidom> *&hom_f, int careful = 0x01,
	chain<euclidom> ***gfgen = 0,
	gcomplex<tCell2l<typename cubetype::CellType>,euclidom>
	**gfcompl = 0, chain<euclidom> ***gygen = 0,
	gcomplex<tCell2l<typename cubetype::CellType>,euclidom>
	**gycompl = 0)
{
	// define the type of a 2-layer cube and 2-layer cell
	typedef tCube2l<cubetype> cube2ltype;
	typedef typename cube2ltype::CellType cell2ltype;

	// turn off locally the usage of binary decision diagrams
	local_var<int> TurnOffMaxBddDim (MaxBddDim, 0);

	// transform the 'careful' bits into separate variables
	bool verify = careful & 0x01;
	bool checkacyclic = careful & 0x02;

	// remove from X cubes which are in A
	removeAfromX (Xcubes0, Acubes0, "X", "A");

	// leave in A only the neighbors of X\\A
	restrictAtoneighbors (Xcubes0, Acubes0, "X", "A");

	// if the set X is empty, the answer is obvious
	if (Xcubes0. empty ())
	{
		sout << "X is a subset of A. The homology of (X,A) "
			"is trivial and the map is 0.";
		return -1;
	}

	// ----- define the layers ------

	// define the two-layer structure
	sout << "Defining the two-layer structure... ";
	cube2ltype::setlayers (Xcubes0, Acubes0);

	// transform the cubes in X and in A to the two-layer sets
	hashedset<cube2ltype> Xcubes;
	for (int_t i = 0; i < Xcubes0. size (); ++ i)
		Xcubes. add (cube2ltype (Xcubes0 [i], 1));
	hashedset<cube2ltype> Acubes;
	for (int_t i = 0; i < Acubes0. size (); ++ i)
		Acubes. add (cube2ltype (Acubes0 [i], 0));

	// say that defining the two-layer structure is done
	sout << cube2ltype::layer1 (). size () << "+" <<
		cube2ltype::layer0 (). size () << " cubes, " <<
		cell2ltype::identify (). size () << " cells.\n";

	// ----- transform the map ------

	// determine Y and B
	sout << "Creating the sets Y and B... ";
	hashedset<cube2ltype> Ycubes (Xcubes);
	hashedset<cube2ltype> Bcubes (Acubes);
	for (int_t i = 0; i < Xcubes0. size (); ++ i)
	{
		const hashedset<cubetype> &img = Fcubmap0 (Xcubes0 [i]);
		for (int_t j = 0; j < img. size (); ++ j)
		{
			if (!Xcubes0. check (img [j]))
				Bcubes. add (cube2ltype (img [j], 0));
		}
	}
	for (int_t i = 0; i < Acubes0. size (); ++ i)
	{
		const hashedset<cubetype> &img = Fcubmap0 (Acubes0 [i]);
		for (int_t j = 0; j < img. size (); ++ j)
			Bcubes. add (cube2ltype (img [j], 0));
	}
	sout << Ycubes. size () << " cubes in Y\\B, " <<
		Bcubes. size () << " in B.\n";

	// lift the map to the two-layer structure
	mvmap<cube2ltype,cube2ltype> Fcubmap;
	for (int_t i = 0; i < Xcubes0. size (); ++ i)
	{
	//	Fcubmap [Xcubes [i]]. size ();
		const hashedset<cubetype> &img = Fcubmap0 (Xcubes0 [i]);
		if (img. empty ())
			throw "Empty image of a box in X.\n";
		for (int_t j = 0; j < img. size (); ++ j)
		{
			int layer = Xcubes0. check (img [j]) ? 1 : 0;
			Fcubmap [Xcubes [i]]. add
				(cube2ltype (img [j], layer));
		}
	}
	for (int_t i = 0; i < Acubes0. size (); ++ i)
	{
	//	Fcubmap [Acubes [i]]. size ();
		const hashedset<cubetype> &img = Fcubmap0 (Acubes0 [i]);
		if (img. empty ())
			throw "Empty image of a box in A.\n";
		for (int_t j = 0; j < img. size (); ++ j)
			Fcubmap [Acubes [i]]. add
				(cube2ltype (img [j], 0));
	}

	// forget the initial single-layer sets and the map
	{
		hashedset<cubetype> empty;
		Xcubes0 = empty;
		Acubes0 = empty;
	}
	{
		mvmap<cubetype,cubetype> empty;
		Fcubmap0 = empty;
	}

	// remember the original size of the set A and of the set X
	int_t origAsize = Acubes. size ();
	int_t origXsize = Xcubes. size ();

	// determine the dimension of X and Y if possible
	int Xspacedim = Xcubes. empty () ? -1 : Xcubes [0]. dim ();
	int Yspacedim = Ycubes. empty () ? -1 : Ycubes [0]. dim ();

	// ----- reduce the sets of cubes -----

	// prepare the set of cubes to keep in X (unused in this program)
	hashedset<cube2ltype> Xkeepcubes;

	// allocate a suitable bit field set for the reduction and show msg
	if (Xspacedim > 0)
		knownbits [Xspacedim];

	// reduce the pair of sets of cubes (X,A) without acyclicity check
	if (!Acubes. empty () && !checkacyclic)
	{
		// reduce the pair (X,A)
		reducepair (Xcubes, Acubes, Xkeepcubes, "X", "A");

		// if nothing remains in X, then the result is trivial
		if (Xcubes. empty ())
		{
			sout << "There are no cubes left "
				"in X\\A. The homology of (X,A) "
				"is trivial and the map is 0.";
			return -1;
		}
	}

	// remember which inclusions have been verified
	bool inclFABchecked = false;
	bool inclFXYchecked = false;

	// do the careful or extended reduction
	if (checkacyclic)
	{
		// check if F (X\A) \subset Y
		if (verify)
		{
			checkimagecontained (Fcubmap,
				Xcubes, Ycubes, Bcubes,
				Acubes. empty () ? "X" : "X\\A", "Y");
			inclFXYchecked = true;
		}
		// check if F (A) \subset B and if F (A) is disjoint from Y
		if (verify && !Acubes. empty ())
		{
			checkimagecontained (Fcubmap, Acubes, Bcubes,
				"A", "B");
			checkimagedisjoint (Fcubmap, Acubes, Ycubes,
				"A", "Y\\B");
			inclFABchecked = true;
		}
	}
	else if (!Acubes. empty ())
	{
		// check if F (X\A) \subset Y
		if (verify)
		{
			checkimagecontained (Fcubmap,
				Xcubes, Ycubes, Bcubes,
				Acubes. empty () ? "X" : "X\\A", "Y");
			inclFXYchecked = true;
		}
	}

	// expand A within X and modify (Y,B)
	if (!Acubes. empty ())
	{
		// expand A towards X and modify (Y,B) accordingly
		expandAinX (Xcubes, Acubes, Ycubes, Bcubes, Fcubmap,
			"X", "A", "B", true /*indexmap*/, checkacyclic);
	}

	// reduce the pair (X,A) or the set X with acyclicity check
	if (checkacyclic)
	{
		// leave in A only the neighbors of X\\A
		restrictAtoneighbors (Xcubes, Acubes, "X", "A");

		// reduce the pair (X,A) with acyclicity check
		reducepair (Xcubes, Acubes, Fcubmap, Xkeepcubes, "X", "A");

		// if nothing remains in X, then the result is trivial
		if (Xcubes. empty ())
		{
			sout << "There are no cubes left "
				"in X\\A. The homology of (X,A) "
				"is trivial and the map is 0.";
			return -1;
		}
	}

	// reduce the pair (X,A) even further
	if (!checkacyclic && !Acubes. empty ())
	{
		// leave in A only the neighbors of X\\A
		restrictAtoneighbors (Xcubes, Acubes, "X", "A");

		// continue the reduction of the pair (X,A)
		reducepair (Xcubes, Acubes, Xkeepcubes, "X", "A");
	}

	// indicate that the acyclicity of the map should be verified
	if (!verify)
	{
		if (!checkacyclic && ((origAsize != Acubes. size ()) ||
			(origXsize != Xcubes. size ())))
		{
			sout << "*** Important note: X or A changed. "
				"You must make sure\n"
				"*** that the restriction of F "
				"to the new sets is acyclic.\n";
		}
		else
		{
			sout << "*** Note: The program assumes "
				"that the input map is acyclic.\n";
		}
	}

	// check if F (X\A) \subset Y
	if (verify && !inclFXYchecked)
	{
		checkimagecontained (Fcubmap, Xcubes, Ycubes, Bcubes,
			Acubes. empty () ? "X" : "X\\A", "Y");
		inclFXYchecked = true;
	}

	// check if F (A) \subset B [this should always be satisfied]
	if (verify && !inclFABchecked && !Acubes. empty ())
	{
		checkimagecontained (Fcubmap, Acubes, Bcubes, "A", "B");
		checkimagedisjoint (Fcubmap, Acubes, Ycubes, "A", "Y\\B");
		inclFABchecked = true;
	}

	// set the union of the domain of the map of interest
	// and the image of the map as the cubes to keep in Y
	hashedset<cube2ltype> Ykeepcubes;
	addmapimg (Fcubmap, Xcubes, Acubes, Ykeepcubes,
		true /*indexmap*/);

	// reduce the pair of cubical sets (Y,B) towards the image of F
	if (Xspacedim == Yspacedim)
	{
		expandAinX (Ycubes, Bcubes, "Y", "B");
		restrictAtoneighbors (Ycubes, Bcubes, "Y", "B", &Ykeepcubes);
		reducepair (Ycubes, Bcubes, Ykeepcubes, "Y", "B");
	}

	// ----- create the cubical complexes -----

	// transform the set of cubes X into a set of cells,
	// but do not forget Xcubes yet
	gcomplex<cell2ltype,euclidom> Xcompl;
	cubes2cells (Xcubes, Xcompl, Acubes. size () ? "X\\A" : "X", false);

	// transform the set of cubes A into a set of cubical cells
	// but do not forget Acubes yet
	gcomplex<cell2ltype,euclidom> Acompl;
	cubes2cells (Acubes, Acompl, "A", false);

	// if the set X is empty, no computations are necessary
	if (Xcompl. empty ())
	{
		if (!Acompl. empty ())
			sout << "The set X is contained in A. "
				"The homology of (X,A) is trivial.";
		else
			sout << "The set X is empty. "
				"The homology of X is trivial.";
		return -1;
	}

	// transform the cubes in Y into cubical cells and forget the cubes
	gcomplex<cell2ltype,euclidom> *Ycompl =
		new gcomplex<cell2ltype,euclidom>;
	cubes2cells (Ycubes, *Ycompl, Bcubes. empty () ? "Y" : "Y\\B");
	if (!Ycubes. empty ())
	{
		hashedset<cube2ltype> empty;
		Ycubes = empty;
	}

	// transform the cubes in B into cubical cells and forget the cubes
	gcomplex<cell2ltype,euclidom> Bcompl;
	cubes2cells (Bcubes, Bcompl, "B");
	if (!Bcubes. empty ())
	{
		hashedset<cube2ltype> empty;
		Bcubes = empty;
	}

	// transform the cubes to keep in Y into cells and forget the cubes
	gcomplex<cell2ltype,euclidom> Ykeepcompl;
	cubes2cells (Ykeepcubes, Ykeepcompl, "Ykeep");
	if (!Ykeepcubes. empty ())
	{
		hashedset<cube2ltype> empty;
		Ykeepcubes = empty;
	}

	// determine the dimension of X and Y as cubical complexes
	int Xdim = Xcompl. dim ();
	if ((Xspacedim < 0) && (Xdim >= 0))
		Xspacedim = Xcompl [Xdim] [0]. spacedim ();
	int Ydim = Ycompl -> dim ();
	if ((Yspacedim < 0) && (Ydim >= 0))
		Yspacedim = (*Ycompl) [Ydim] [0]. spacedim ();

	// ----- collapse the cubical sets (X,A) -----

	// create an empty set of cells to keep in X
	gcomplex<cell2ltype,euclidom> Xkeepcompl;

	// reduce the pair of sets (Xcompl, Acompl) while adding to them
	// boundaries of all the cells
	collapse (Xcompl, Acompl, Xkeepcompl, "X", "A",
		true, true, false);

	// if nothing remains in X, then the result is trivial
	if (Xcompl. empty ())
	{
		sout << "Nothing remains in X. "
			"The homology of (X,A) is trivial.";
		return -1;
	}

	// forget the cells to keep in X
	if (!Xkeepcompl. empty ())
	{
		gcomplex<cell2ltype,euclidom> empty;
		Xkeepcompl = empty;
	}

	// make a correction to the dimension of X
	if (Xdim != Xcompl. dim ())
	{
		sout << "Note: The dimension of X decreased from " <<
			Xdim << " to " << Xcompl. dim () << ".\n";

		Xdim = Xcompl. dim ();
	}

	// ----- create a reduced graph of F -----

	// create the map F defined on the cells in its domain
	mvcellmap<cell2ltype,euclidom,cube2ltype> Fcellcubmap (Xcompl);
	sout << "Creating the map F on cells in X... ";
	int_t countimages = createimages (Fcellcubmap, Fcubmap, Fcubmap,
		Xcubes, Acubes);
	sout << countimages << " cubes added.\n";

	// forget the full cubical set X
	if (Xcubes. size ())
	{
		hashedset<cube2ltype> empty;
		Xcubes = empty;
	}

	// create the map F defined on the cells in its domain subcomplex A
	mvcellmap<cell2ltype,euclidom,cube2ltype> FcellcubmapA (Acompl);
	if (!Acompl. empty ())
	{
		sout << "Creating the map F on cells in A... ";
		int_t count = createimages (FcellcubmapA, Fcubmap, Acubes);
		sout << count << " cubes added.\n";
	}

	// forget the full cubical set A
	if (Acubes. size ())
	{
		hashedset<cube2ltype> empty;
		Acubes = empty;
	}

	// create the graph of F as a cubical cell complex
	gcomplex<cell2ltype,euclidom> *Fcompl =
		new gcomplex<cell2ltype,euclidom>;
	sout << "Creating a cell map for F... ";
	mvcellmap<cell2ltype,euclidom,cell2ltype> Fcellmap (Xcompl);
	bool acyclic = createcellmap (Fcellcubmap, FcellcubmapA,
		Fcellmap, verify);
	sout << "Done.\n";
	if (checkacyclic && !acyclic)
	{
		sout << "*** SERIOUS PROBLEM: The map is not "
			"acyclic. THE RESULT WILL BE WRONG.\n"
			"*** You must verify the acyclicity of the "
			"initial map with 'chkmvmap'\n"
			"*** and, if successful, run this program "
			"with the '-a' switch.\n";
	}
	if (checkacyclic && acyclic)
	{
		sout << "Note: It has been verified successfully "
			"that the map is acyclic.\n";
	}

	sout << "Creating the graph of F... ";
	creategraph (Fcellmap, *Fcompl, false);
	sout << Fcompl -> size () << " cells added.\n";

	// forget the cubical map on the cells
	{
		mvcellmap<cell2ltype,euclidom,cube2ltype> empty;
		Fcellcubmap = empty;
		FcellcubmapA = empty;
	}

	// ----- collapse the cubical sets (Y,B) -----

	// decrease the dimension of B to the dimension of Y
	decreasedimension (Bcompl, Ydim, "B");

	// create a full cubical complex (with all the faces) of Y\B
	if (!Ycompl -> empty ())
	{
		addboundaries (*Ycompl, Bcompl, 0, false, "Y", "B");

		// forget the cubical complex of B
		if (!Bcompl. empty ())
		{
			sout << "Forgetting " << Bcompl. size () <<
				" cells from B.\n";
			gcomplex<cell2ltype,euclidom> empty;
			Bcompl = empty;
		}
	}

	// collapse the codomain of the map towards the image of F
	{
		sout << "Computing the image of F... ";
		int_t prev = Ykeepcompl. size ();
		project (*Fcompl, Ykeepcompl, *Ycompl, Xspacedim, Yspacedim,
			0, 0, false);
		project (*Fcompl, Ykeepcompl, *Ycompl, 0, Xspacedim,
			Yspacedim, 0, false);
		sout << (Ykeepcompl. size () - prev) << " cells added.\n";

		sout << "Collapsing Y towards F(X)... ";
		gcomplex<cell2ltype,euclidom> empty;
		int_t count = Ycompl -> collapse (empty, Ykeepcompl,
			0, 0, 0, 0);
		sout << 2 * count << " cells removed, " <<
			Ycompl -> size () << " left.\n";
	}

	// forget the cells to keep in Y
	if (!Ykeepcompl. empty ())
	{
		gcomplex<cell2ltype,euclidom> empty;
		Ykeepcompl = empty;
	}

	// make a correction to the dimension of Y
	if (Ydim != Ycompl -> dim ())
	{
		sout << "Note: The dimension of Y decreased from " <<
			Ydim << " to " << Ycompl -> dim () << ".\n";

		Ydim = Ycompl -> dim ();
	}

	// ----- create chain complexes from the cubical sets ------

	// create a chain complex from X (this is a relative chain complex!)
//	chaincomplex<euclidom> cx (Xcompl. dim (), false /*generators*/);

	// create a chain complex from the graph of F (it is relative)
	chaincomplex<euclidom> cgraph (Fcompl -> dim (), false);
	sout << "Creating the chain complex of the graph of F... ";
	createchaincomplex (cgraph, *Fcompl);
	sout << "Done.\n";

	// create the chain complex from Y (this is a relative complex)
	chaincomplex<euclidom> cy (Ydim, false);
	sout << "Creating the chain complex of Y... ";
	createchaincomplex (cy, *Ycompl);
	sout << "Done.\n";

	// create the projection map from the graph of the map to Y
	chainmap<euclidom> cmap (cgraph, cy);
	sout << "Creating the chain map of the projection... ";
	createprojection (*Fcompl, *Ycompl, cmap, Xspacedim,
		Yspacedim, 0);
	sout << "Done.\n";

	// if this is an index map, create the projection map from the graph
	// of the map to X composed with the inclusion into Y
	chainmap<euclidom> imap (cgraph, cy);
	sout << "Creating the chain map of the inclusion... ";
	createprojection (*Fcompl, *Ycompl, imap, 0, Xspacedim, Yspacedim);
	sout << "Done.\n";

	// forget the graph of F if it is not going to be used anymore
	if (gfcompl)
		(*gfcompl) = Fcompl;
	else
		delete Fcompl;

	// forget the cubical complex Y unless requested to keep it
	if (gycompl)
		(*gycompl) = Ycompl;
	else
		delete Ycompl;

	// ----- compute and show homology, save generators -----

	// prepare the name of the graph of F
	word gFname;
	gFname << "the graph of " << Fname;

	// compute the homology of the chain complex of the graph of the map
	int maxlevel_cx = Homology (cgraph, gFname, hom_cx);

	// extract the computed generators of the graph if requested to
	if (gfgen)
		*gfgen = ExtractGenerators (cgraph, hom_cx, maxlevel_cx);

	// compute the homology of the chain complex of Y
	chain<euclidom> *hom_cy = 0;
	int maxlevel_cy = Homology (cy, Xname, hom_cy);

	// extract the computed generators of Y if requested to
	if (gygen)
		*gygen = ExtractGenerators (cy, hom_cy, maxlevel_cy);

	// ----- show the map(s) -----

	// determine the maximal non-trivial homology level for maps
	int homdimgraph = cgraph. dim ();
	while ((homdimgraph >= 0) && (!hom_cx [homdimgraph]. size ()))
		-- homdimgraph;
	int homdimy = cy. dim ();
	while ((homdimy >= 0) && (!hom_cy [homdimy]. size ()))
		-- homdimy;
//	sout << "Maximal homology level considered for the map "
//		"is " << homdim << ".\n";

	// prepare the data structures for the homology
	chaincomplex<euclidom> hgraph (homdimgraph);
	chaincomplex<euclidom> hy (homdimy);
	chainmap<euclidom> *hmap = new chainmap<euclidom> (hgraph, hy);
	chainmap<euclidom> hincl (hgraph, hy);
	chainmap<euclidom> *hcomp = new chainmap<euclidom> (hgraph, hgraph);

	// show the map induced in homology by the chain map
	sout << "The map induced in homology is as follows:\n";
	hgraph. take_homology (hom_cx);
	hy. take_homology (hom_cy);
	hmap -> take_homology (cmap, hom_cx, hom_cy);
	hmap -> show (sout, "\tf", "x", "y");

	// show the map induced in homology by the inclusion map
	sout << "The map induced in homology by the inclusion:\n";
	hincl. take_homology (imap, hom_cx, hom_cy);
	hincl. show (sout, "\ti", "x", "y");

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
		hincl. show (sout, "\tI", "y", "x");

		sout << "The composition of F and the inverse "
			"of the map induced by the inclusion:\n";
		hcomp -> compose (hincl, *hmap);
		hcomp -> show (sout, "\tF", "x", "x");
	}

	// set the appropriate map
	if (invertible)
	{
		hom_f = hcomp;
		delete hmap;
	}
	else
	{
		hom_f = hmap;
		delete hcomp;
	}

	// throw an exception if the map is not invertible
	if (!invertible)
		throw "Unable to invert the inclusion map.";

	maxlevel = (maxlevel_cx < maxlevel_cy) ? maxlevel_cx : maxlevel_cy;
	return maxlevel;
} /* Homology2l */

/// A version of the above procedure with the default names.
template <class euclidom, class cubetype>
int Homology2l (mvmap<cubetype,cubetype> &Fcubmap,
	hashedset<cubetype> &Xcubes, hashedset<cubetype> &Acubes,
	chain<euclidom> *&hom, int &maxlevel,
	chainmap<euclidom> *&hom_f, int careful = 0x01,
	chain<euclidom> ***gfgen = 0,
	gcomplex<tCell2l<typename cubetype::CellType>,euclidom>
	**gfcompl = 0, chain<euclidom> ***gygen = 0,
	gcomplex<tCell2l<typename cubetype::CellType>,euclidom>
	**gycompl = 0)
{
	return Homology2l (Fcubmap, "F", Xcubes, "X", Acubes, "A", hom,
		maxlevel, hom_f, careful, gfgen, gfcompl, gygen, gycompl);
} /* Homology2l */


// --------------------------------------------------
// ------------ ACYCLICITY VERIFICATION -------------
// --------------------------------------------------

/// Verifies whether the neighborhood of q in X is acyclic.
/// Uses BDDs for dimensions 2 and 3, and computes homology otherwise.
inline bool acyclic (const cube &q, const cubes &X)
{
	int dim = q. dim ();
	BitField b;
	int_t maxneighbors = getmaxneighbors (dim);
	b. allocate (maxneighbors);
	bool result = acyclic (q, dim, X, &b, maxneighbors);
	b. free ();
	return result;
} /* acyclic */


// --------------------------------------------------
// ------------- BINARY CUBE FUNCTIONS --------------
// --------------------------------------------------

/// Computes the Betti Numbers of a set of full cubes in a bincube.
/// This procedure makes use of the technique of splitting the set
/// of cubes into connected components and computing relative homology
/// of each component with respect to some cube in each of them.
template <int dim, int twoPower>
void ComputeBettiNumbers (bincube<dim,twoPower> &b, int *result)
{
	using namespace capd::homology;
	typedef typename bincube<dim,twoPower>::iterator cubetype;
	typedef typename bincube<dim,twoPower>::neighborhood_iterator
		neighbortype;

	// perform the reduction of full cubes in the binary cube first
	sout << "Reducing the binary cube";
	int prev = b. count ();
	reduceFullCubes (b);
	sout << (prev - b. count ()) << " cubes removed, " <<
		b. count () << " left.\n";

	// create an extra binary cube to store connected components
	bincube<dim,twoPower> c;

	// set the correct wrapping for the new binary cube and the space
	coordinate wrap [dim];
	bool setwrapping = false;
	for (int i = 0; i < dim; ++ i)
	{
		if (b. wrapped (i))
		{
			wrap [i] = 1 << twoPower;
			setwrapping = true;
			c. wrap (i);
		}
		else
			wrap [i] = 0;
	}
	if (setwrapping)
		tPointBase<coordinate>::setwrapping (wrap);

	// reset the table to store Betti numbers
	for (int i = 0; i <= dim; ++ i)
		result [i] = 0;

	// gather Betti numbers for each connected component separately
	bool first_run = true;
	while (!b. empty ())
	{
		// increase the 0th Betti number which counts conn. comp.
		++ *result;

		// extract a connected component
		if (first_run)
			first_run = false;
		else
			c. clear ();
		hashIntQueue s;
		s. push (static_cast<int> (b. begin ()));
		while (!s. empty ())
		{
			int n = s. front ();
			s. pop ();
			neighbortype cur = b. neighborhood_begin (n);
			neighbortype end = b. neighborhood_end (n);
			while (cur != end)
			{
				s. push (static_cast<int> (cur));
				++ cur;
			}
			c. add (n);
			b. remove (n);
		}

		// if the component has just one cube, the answer is obvious
		if (c. count () == 1)
			continue;

		// transform the binary cube into the usual set of cubes
		// (in the future this step will be postponed)
		SetOfCubes X;
		cubetype cur (c. begin ()), end (c. end ());
		while (cur != end)
		{
			X. add (cube_cast<Cube> (cur));
			++ cur;
		}

		// say which connected component is processed
		sout << "Connected component no. " << *result <<
			" (" << X. size () << " cubes):\n";

		// prepare a pair of sets for relative homology computation
		SetOfCubes A;
		int_t number = X. size () - 1;
		A. add (X [number]);
		X. removenum (number);
		
		// compute the relative homology
		Chain *chn = 0;
		int maxlevel = Homology (X, "X", A, "A", chn);

		// display the result
		ShowHomology (chn, maxlevel);

		// update the Betti number count
		for (int i = 1; i <= maxlevel; ++ i)
			result [i] += BettiNumber (chn [i]);

		// release the memory assigned to the table of chains
		if (chn)
			delete [] chn;
	}
	
	sout << "Computed Betti numbers:";
	for (int i = 0; i <= dim; ++ i)
		sout << " " << result [i];
	sout << ".\n";

	return;
} /* ComputeBettiNumbers */

/// Computes the Betti Numbers of the Homology of a full cubical set
/// defined by means of an n-dimensional bitmap. The size of this bitmap
/// in each direction must equal 2^n, where n=twoPower. The subsequent
/// bits of the binary buffer correspond to the cubes (0,0,...,0),
/// (1,0,...,0), (2,0,...,0), ..., (2^n-1,0,...,0), then
/// (0,1,0,...,0), (1,1,0,...,0), ..., (2^n-1,1,0,...,0), ...,
/// (2^n-1,...,2^n-1). That is, the first coordinate changes the fastest,
/// the second changes less frequently, and the last one changes the slowest.
template <int dim, int twoPower, class coordtype>
void ComputeBettiNumbers (char *binary_buffer, int *result,
	const coordtype *space_wrapping = 0)
{
	using namespace capd::homology;

	// create a binary cube based on the binary buffer
	bincube<dim,twoPower> b (binary_buffer);
	
	// set the space wrapping if requested to
	if (space_wrapping)
	{
		for (int i = 0; i < dim; ++ i)
		{
			if (!space_wrapping [i])
				continue;
			int w = space_wrapping [i];
			if (w != (1 << twoPower))
				sout << "WARNING: Wrapping [" << i <<
					"] set to " << (1 << twoPower) <<
					".\n";
			b. wrap (i);
		}
	}

	ComputeBettiNumbers (b, result);
	return;
} /* ComputeBettiNumbers */


// --------------------------------------------------
// -------------- SIMPLIFIED INTERFACE --------------
// --------------------------------------------------

/// Computes the Betti numbers of the given set of full cubes.
/// \param coord - a table of coordinates of all the cubes;
/// the <i>i</i>-th coordinate of the <i>k</i>-th cube is stored
/// in coord [<i>dim</i> * <i>k</i> + <i>i</i>]
/// \param n - the number of cubes in the table,
/// \param dim - the space dimension,
/// \param result - a table into which the result is written; its size
/// must be at least (<i>dim</i> + 1),
template <class coordtype>
void ComputeBettiNumbers (coordtype *coord, int n, int dim, int *result)
{
	using namespace capd::homology;

	// create a corresponding set of cubes
	SetOfCubes X;
	coordinate c [Cube::MaxDim];
	coordtype const *coordpointer = coord;
	for (int i = 0; i < n; ++ i)
	{
		for (int j = 0; j < dim; ++ j)
			c [j] = static_cast<coordtype> (*(coordpointer ++));
		X. add (Cube (c, dim));
	}

	// turn off screen output
	bool soutput = sout. show;
	sout. show = false;
	bool coutput = scon. show;
	scon. show = false;
	
	// compute the homology of the constructed cubical set
	Chain *hom;
	int maxlevel = Homology (X, "X", hom);

	// fill out the resulting table of Betti numbers
	for (int j = 0; j <= dim; ++ j)
		result [j] = (j <= maxlevel) ? BettiNumber (hom [j]) : 0;

	// free unused memory and finish
	if (hom)
		delete [] hom;
	sout. show = soutput;
	scon. show = coutput;
	return;
} /* ComputeBettiNumbers */

/// Sets space wrapping in each direction separately.
/// \param dim - the dimension of cubes for which the space wrapping
/// is defined
/// \param wrap - space wrapping: a nonzero entry indicates
/// a periodic boundary condition in the corresponding direction
template <class coordtype>
inline void SetSpaceWrapping (int dim, const coordtype *wrap)
{
	if ((dim < 0) || (dim >= Cube::MaxDim))
		return;

	// set space wrapping if requested to
	coordinate wrapcoord [Cube::MaxDim];
	for (int j = 0; j < dim; ++ j)
		wrapcoord [j] = static_cast <coordtype>
			((wrap [j] >= 0) ? wrap [j] : -wrap [j]);
	tPointBase<coordinate>::setwrapping (wrapcoord, dim, dim + 1);
	return;
} /* SetSpaceWrapping */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_HOMOLOGY_H_ 

/// @}

