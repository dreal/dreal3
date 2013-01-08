/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file indxpalg.h
///
/// This file contains some data structures and functions aimed at
/// computing combinatorial index pairs.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on May 17, 2006. Last revision: August 30, 2006.


#ifndef _CAPD_HOMOLOGY_INDXPALG_H_ 
#define _CAPD_HOMOLOGY_INDXPALG_H_ 

#include "capd/homology/cubisets.h"
#include "capd/homology/cube.h"
#include "capd/homology/cell.h"
#include "capd/homology/digraph.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------------- Map Class --------------------
// --------------------------------------------------

/// This is a general map class that may be inherited
/// by your particular class that computes a map.
template <class TCube, class TSetOfCubes>
class MapClass
{
public:
	/// Computes the image of a cube under the map
	/// and adds the image cubes to the given set.
	const TSetOfCubes &operator () (const TCube &q) const
	{
		throw "The map has not been defined.";
	}

}; /* class MapClass */


/// This class is a wrapper for a map that computes the image of a cube
/// as a rectangular box (i.e., using the interval arithmetic).
/// Additionally, each object of this class stores all the previously
/// computed values for quick reference.
template <class TCube = Cube>
class BufferedMapClass: public MapClass<TCube,hashedset<TCube> >
{
public:
	/// The type of the set of cubes.
	typedef hashedset<TCube> TSetOfCubes;

	/// The type of coordinates of a cube.
	typedef typename TCube::CoordType TCoordType;
	
	/// The class of a map that computes the image of a unitary cube.
	typedef int (*map) (const TCoordType *coord,
		double *left, double *right);

	/// The constructor.
	BufferedMapClass (map _f): f (_f) {}

	/// Computes the image of a cube under the map
	/// and adds the image cubes to the given set.
	const TSetOfCubes &operator () (const TCube &q) const;

	/// The multivalued cubical map computed so far.
	mutable mvmap<TCube,TCube> F;

private:
	/// A pointer to the map which computes images of cubes.
	map f;

}; /* class BufferedMapClass */

template <class TCube>
const typename BufferedMapClass<TCube>::TSetOfCubes &
	BufferedMapClass<TCube>::operator () (const TCube &q) const
{
	// if the image of the cube is already known, then return it
	const TSetOfCubes &dom = F. getdomain ();
	if (dom. check (q))
		return F (q);

	// determine the dimension
	const int dim = q. dim ();
	
	// compute the image of the cube
	TCoordType *coord = new TCoordType [dim];
	q. coord (coord);
	double *left = new double [dim];
	double *right = new double [dim];
	f (coord, left, right);
	delete [] coord;

	// compute the minimal and maximal corner of the rectangular
	// cubical set that covers the computed image of the cube
	TCoordType *ileft = new TCoordType [dim];
	TCoordType *iright = new TCoordType [dim];
	for (int i = 0; i < dim; ++ i)
	{
		ileft [i] = static_cast<TCoordType> (left [i]);
		if ((ileft [i] + 1 < left [i]) ||
			(ileft [i] - 1 > left [i]))
			throw "Conversion error: double to coord - "
				"out of range.";
		for (int j = 0; j < 10; ++ j)
		{
			if (ileft [i] >= left [i])
				-- ileft [i];
			else
				break;
		}
		if (ileft [i] >= left [i])
			throw "Outer approximation failure (left).";
		iright [i] = static_cast<TCoordType> (right [i]);
		if ((iright [i] + 1 < right [i]) ||
			(iright [i] - 1 > right [i]))
			throw "Conversion error: double to coord - "
				"out of range.";
		for (int j = 0; j < 10; ++ j)
		{
			if (iright [i] <= right [i])
				++ iright [i];
			else
				break;
		}
		if (iright [i] <= right [i])
			throw "Outer approximation failure (right).";
	}
	delete [] right;
	delete [] left;

	// create the image of the cube and add all the cubes to it
	hashedset<TCube> &img = F [q];
	tRectangle<TCoordType> r (ileft, iright, dim);
	const TCoordType *c;
	while ((c = r. get ()) != 0)
		img. add (TCube (c, dim));
	delete [] iright;
	delete [] ileft;

	// return the image of the cube
	return F (q);
} /* operator () */

template <class TCube>
std::ostream &operator << (std::ostream &out,
	const BufferedMapClass<TCube> &map)
{
	out << map. F;
	return out;
} /* operator << */


// --------------------------------------------------
// ------------------ Neighborhood ------------------
// --------------------------------------------------

/// Computes a cubical neighborhood of width 1 around the set.
template <class TSetOfCubes>
int neighborhood (const TSetOfCubes &X, TSetOfCubes &result)
{
	// extract the necessary types and constants
	using namespace capd::homology;
	typedef typename TSetOfCubes::value_type cubetype;
	typedef typename cubetype::CoordType coordtype;
	typedef tRectangle<coordtype> rectangle;
	const int maxdim = cubetype::MaxDim;

	// create arrays for the corners of a rectangle around each cube
	coordtype mincoord [maxdim], maxcoord [maxdim];

	// for all the cubes in X
	int_t ncount = X. size ();
	for (int_t n = 0; n < ncount; ++ n)
	{
		// get the coordinates of the cube
		int dim = X [n]. dim ();
		X [n]. coord (mincoord);

		// prepare the corners of a rectangle for the cube
		// and its neighbors
		for (int i = 0; i < dim; ++ i)
		{
			maxcoord [i] = mincoord [i];
			++ maxcoord [i];
			++ maxcoord [i];
			-- mincoord [i];
		}

		// add cubes from the rectangle to the resulting set
		rectangle r (mincoord, maxcoord, dim);
		const coordtype *c;
		while ((c = r. get ()) != 0)
			result. add (cubetype (c, dim));
	}
	return 0;
} /* neighborhood */


// --------------------------------------------------
// ----------------- Invariant Part -----------------
// --------------------------------------------------

/// Computes X := Inv (X). New algorithm by Bill Kalies and Hyunju Ban.
/// If the graph 'gInv' is given, then the resulting graph is created,
/// otherwise only the set X is modified.
template <class TSetOfCubes, class TMap>
void invariantpart (TSetOfCubes &X, const TMap &F, TSetOfCubes &result)
{
	// do nothing if the set X is empty
	int_t ncount = X. size ();
	if (!ncount)
		return;

	// create a digraph of the map
	diGraph<> g;
	for (int_t n = 0; n < ncount; ++ n)
	{
		g. addVertex ();
		const TSetOfCubes &img = F (X [n]);
		int_t icount = img. size ();
		for (int_t i = 0; i < icount; ++ i)
		{
			int_t number = X. getnumber (img [i]);
			if (number < 0)
				continue;
			g. addEdge (number);
		}
	}

	// compute the chain recurrent set of the graph
	// and remember the transposed graph
	multitable<int_t> compVertices, compEnds;
	diGraph<> gT;
	int_t count = SCC (g, compVertices, compEnds,
		static_cast<diGraph<> *> (0), &gT);

	// retrieve vertices that can be reached from the chain recurrent set
	int_t nVertices = ncount;
	char *forward = new char [nVertices];
	for (int_t i = 0; i < nVertices; ++ i)
		forward [i] = 0;
	for (int_t cur = 0; cur < count; ++ cur)
	{
		g. DFScolor (forward, '\1',
			compVertices [cur ? compEnds [cur - 1] :
			static_cast<int_t> (0)]);
	}

	// retrieve vertices that can reach the chein recurrent set
	char *backward = new char [nVertices];
	for (int_t i = 0; i < nVertices; ++ i)
		backward [i] = 0;
	for (int_t cur = 0; cur < count; ++ cur)
	{
		gT. DFScolor (backward, '\1',
			compVertices [cur ? compEnds [cur - 1] :
			static_cast<int_t> (0)]);
	}

	// compute the new set of cubes
	for (int_t i = 0; i < nVertices; ++ i)
		if (forward [i] && backward [i])
			result. add (X [i]);

	// clean the memory and return
	delete [] backward;
	delete [] forward;
	return;
} /* invariantpart */


// --------------------------------------------------
// ------------------- inclusion --------------------
// --------------------------------------------------

/// Verifies if X is a subset of Y. Returns true if yes, false if not.
template <class HSet>
bool inclusion (const HSet &X, const HSet &Y)
{
	int_t countX = X. size ();
	if (countX && Y. empty ())
		return false;

	for (int_t i = 0; i < countX; ++ i)
		if (!Y. check (X [i]))
			return false;
	return true;
} /* inclusion */


// --------------------------------------------------
// ------------------ Index Pair M ------------------
// --------------------------------------------------

/// Computes iteratively Q2 := (F (Q1 + Q2) - Q1) * N.
template <class TSetOfCubes, class TMap>
int ExitSetM (const TSetOfCubes &N, const TSetOfCubes &Q1,
	const TMap &F, TSetOfCubes &resultQ2)
{
	// compute Q2 := (F (Q1 \cup Q2) \setminus Q1) \cap N
	int_t countQ1 = Q1. size ();
	int_t n = 0;

	// for all the cubes in Q1 and Q2
	while (n < countQ1 + resultQ2. size ())
	{
		// compute the image of the cube
		const TSetOfCubes &img =
			F ((n < countQ1) ? Q1 [n] : resultQ2 [n - countQ1]);

		// add those image cubes to Q2 which are in N \setminus Q1
		int_t countImg = img. size ();
		for (int_t i = 0; i < countImg; ++ i)
		{
			if (!N. check (img [i]))
				continue;
			if (Q1. check (img [i]))
				continue;
			resultQ2. add (img [i]);
		}
		++ n;
	}
	return 0;
} /* ExitSetM */

/// Constructs a combinatorial index pair satisfying Mrozek's definition.
/// The initial set S must be invariant, or otherwise some of its cubes
/// may not be included in the resulting invariant set.
template <class TSetOfCubes, class TMap>
int IndexPairM (const TMap &F, const TSetOfCubes &initialS,
	TSetOfCubes &resultQ1, TSetOfCubes &resultQ2)
{
	// prepare the initial guess for S and N
	TSetOfCubes S = initialS;
	TSetOfCubes N;
	neighborhood (S, N);

	sout << "Starting with " << S. size () << " cubes in S_0, " <<
		N. size () << " cubes in N.\n";
	while (1)
	{

		// compute S := Inv (N)
		sout << "S := Inv(N)... ";
		scon << "(computing)\b\b\b\b\b\b\b\b\b\b\b";
		TSetOfCubes empty;
		S = empty;
	//	S = initialS;
		invariantpart (N, F, S);
		sout << S. size () << " cubes; o(S) has ";

		// compute N' := o (S)
		TSetOfCubes newN;
		neighborhood (S, newN);
		sout << newN. size () << " cubes.\n";
		
		// if Int (N) contains Inv (N), then exit
		if (inclusion (newN, N))
			break;
		// otherwise take a larget N and repeat
		else
		{
			sout << "Set N := o(S). ";
			N = newN;
		}
	}

	// compute the index pair (Q1 \cup Q2, Q2)
	resultQ1 = S;
	ExitSetM (N, S, F, resultQ2);
	return 0;
} /* IndexPairM */


// --------------------------------------------------
// ------------------ Index Pair P ------------------
// --------------------------------------------------

/// Constructs a combinatorial index pair satisfying Pilarczyk's definition.
/// The initial set S must be an approximation of the invariant set for the
/// map, for example, a rough covering obtained in numerical simulations.
template <class TSetOfCubes, class TMap>
int IndexPairP (const TMap &F, const TSetOfCubes &initialS,
	TSetOfCubes &resultQ1, TSetOfCubes &resultQ2)
{
	resultQ1 = initialS;

	// compute the initial Q2 = f (Q1) - Q1
	sout << "Computing the map on Q1 (" << resultQ1. size () <<
		" cubes)... ";
	for (int_t i = 0; i < resultQ1. size (); ++ i)
	{
		const TSetOfCubes &img = F (resultQ1 [i]);
		for (int_t j = 0; j < img. size (); ++ j)
		{
			if (!resultQ1. check (img [j]))
				resultQ2. add (img [j]);
		}
	}
	sout << resultQ2. size () << " cubes added to Q2.\n";

//	sout << "Starting with " << resultQ1. size () <<
//		" cubes in Q1, " << resultQ2. size () <<
//		" cubes in Q2.\n";

	// compute images of cubes in Q2 and if any of them intersects Q1
	// then move this cube from Q2 to Q1
	sout << "Increasing Q1 and Q2 until F(Q2) is disjoint from Q1... ";
	int_t counter = 0;
	int_t countimages = 0;
	int_t cur = 0;
	TSetOfCubes removed;
	while (1)
	{
		// if there are no cubes in Q2, repeat or finish
		if (cur >= resultQ2. size ())
		{
			if (removed. empty ())
				break;
			resultQ2. remove (removed);
			TSetOfCubes empty;
			removed = empty;
			cur = 0;
			continue;
		}

		// display a counter
		++ counter;
		if (!(counter % 373))
			scon << std::setw (12) << counter <<
				"\b\b\b\b\b\b\b\b\b\b\b\b";

		// verify whether F(q) intersects Q1
		bool intersects = false;
		const TSetOfCubes &img = F (resultQ2 [cur]);
		++ countimages;
		for (int_t j = 0; j < img. size (); ++ j)
		{
			if (resultQ1. check (img [j]))
			{
				intersects = true;
				break;
			}
		}
		
		if (intersects)
		{
			// add F(q)\Q1 to Q2
			for (int_t j = 0; j < img. size (); ++ j)
			{
				if (!resultQ1. check (img [j]))
					resultQ2. add (img [j]);
			}
			// move q from Q2 to Q1
			resultQ1. add (resultQ2 [cur]);
			removed. add (resultQ2 [cur]);
		}

		// take the next cube from Q2
		++ cur;
	}
	sout << countimages << " analyzed.\n";
	return 0;
} /* IndexPairP */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_INDXPALG_H_ 

/// @}

