/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubisets.h
///
/// This file contains various procedures defined on cubical sets
/// and related to some combinatorial operations or homology computation.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: June 25, 2010.


#ifndef _CAPD_HOMOLOGY_CUBISETS_H_ 
#define _CAPD_HOMOLOGY_CUBISETS_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/chains.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/setunion.h"
#include "capd/homology/gcomplex.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cube.h"
#include "capd/homology/cell.h"
#include "capd/homology/cubmaps.h"
#include "capd/homology/neighbor.h"
#include "capd/homology/cubacycl.h"
#include "capd/homology/tabulate.h"
#include "capd/homology/known.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {

// --------------------------------------------------
// ------------ acyclicity verification -------------
// --------------------------------------------------

/// Checks whether this cube's nieghbors form an acyclic set.
/// Returns: 1 = yes for sure, 0 = probably no, but it is not sure.
inline int acyclic (int dim, BitField &b)
{
	// look for the answer in the tabulated data
	const char *table = tabulated [dim];
	if (table)
	{
		return Tabulated::get (table,
			bits2int (b, getmaxneighbors (dim)));
	}

	// look for the answer among the known combinations
	SetOfBitFields *known = knownbits [dim];
	int answer = known ? known -> check (b) : -1;

	// if the answer is known then return it
	if (answer >= 0)
		return answer;

	// create a model cube for building the neighborhood
	coordinate c [Cube::MaxDim];
	for (int i = 0; i < dim; ++ i)
		c [i] = 0;
	Cube qzero (c, dim);

	// find out whether the set of neighbors is acyclic or not
/*	SetOfCubes neighbors;
	addneighbors (qzero, b, neighbors, true);
	SetOfCubes empty;
	cubreducequiet (empty, neighbors, empty, known); // nie ma takiego
	answer = (neighbors. size () == 1);
*/
// /*
	gcomplex<CubicalCell,integer> neighbors;
	addneighbors (qzero, b, neighbors, true);
	answer = static_cast<int> (acyclic (neighbors));
//*/
	// add the answer to the list of known ones
	if (known)
		known -> add (b, answer);

	return answer;
} /* acyclic */

/// Checks thoroughly whether the given set of cubes is acyclic.
/// Returns true if yes, false if not.
template <class tCube>
inline bool acyclic (const hashedset<tCube> &cset)
{
	// the empty set is not acyclic
	if (cset. empty ())
		return false;

	// a singleton is acyclic
	if (cset. size () == 1)
		return true;

	// reduce the set and see if there is only one cube remaining
	hashedset<tCube> emptycubes;
	hashedset<tCube> theset = cset;
	cubreducequiet (emptycubes, theset, emptycubes); // !!!
	if (theset. size () == 1)
		return true;

	// create a cubical complex from this set of cubes
	gcomplex<typename tCube::CellType,integer> ccompl;
	int_t size = cset. size ();
	for (int_t i = 0; i < size; ++ i)
		ccompl. add (typename tCube::CellType (cset [i]));

	// check whether this geometric complex is acyclic or not
	return acyclic (ccompl);
} /* acyclic */

/// Verifies the acyclicity of a neighborhood of the given cube.
/// \param q - the cube whose neighborhood is verified
/// \param dim - the dimension of the cube
/// \param cset - the set to search for the cubes adjacent to <i>q</i>
/// \param b - a pointer to a bitfield in which neighbors are marked
/// \param neighbors - a pointer to a set of cubes to which the neighbors
/// are added (unless BDDs are used) if the pointer is not null
/// \param maxneighbors - the maximal possible number of neighbors:
/// should be equal to 3^<i>dim</i> - 1
/// Uses BDDs if available. Marks verified neighbors in b.
template <class tCube, class tCubeSet1, class tCubeSet2>
inline bool acyclic (const tCube &q, int dim, const tCubeSet1 &cset,
	BitField *b, int_t maxneighbors, tCubeSet2 *neighbors)
{
	// use a binary decision diagram code if possible
	if (dim <= MaxBddDim)
		return bddacyclic (q, dim, cset, *b);

	// get the neighbors of the cube
	int_t n = getneighbors (q, b, cset, neighbors, 0);

	// if the answer is obvious from the number of neighbors, return it
	if ((n == 0) || (n == maxneighbors))
		return false;
	if (n == 1)
		return true;

	// return the information on whether this set of neighbors is acyclic
	return acyclic (dim, *b);
} /* acyclic */

/// Verifies the acyclicity of a neighborhood of the given cube.
/// Calls the above procedure with a null pointer to the set of neighbors.
template <class tCube, class tCubeSet>
inline bool acyclic (const tCube &q, int dim, const tCubeSet &cset,
	BitField *b, int_t maxneighbors)
{
	hashedset<tCube> *neighbors = 0;
	return acyclic (q, dim, cset, b, maxneighbors, neighbors);
} /* acyclic */

/// Verifies whether a cube from the other set can be removed.
template <class tCube>
bool acyclic_rel (const tCube &q, int dim, const hashedset<tCube> &cset,
	const hashedset<tCube> &other, BitField *b, int_t maxneighbors,
	hashedset<tCube> *neighbors_main, hashedset<tCube> *neighbors_other)
{
	// use a binary decision diagram code if possible
	if (dim <= MaxBddDim)
	{
		if (!getneighbors (q, b, cset, 1))
			return true;
		if (!bddacyclic (q, dim, other, *b))
			return false;
		return bddacyclic (q, dim, makesetunion (cset, other), *b);
	}

	// get the neighbors from the other set
	int_t nother = getneighbors (q, b, other, neighbors_other, 0);

	// verify if this set of neighbors is acyclic
	bool otheracyclic = (nother < maxneighbors) &&
		((nother == 1) || (nother && acyclic (dim, *b)));

	// add the neighbors from 'cset'
	int_t ncset = getneighbors (q, b, cset, neighbors_main, 0);

	// if there are no cubes in 'cset', then this cube is ok
	if (!ncset)
		return true;

	// if there are neighbors in 'cset' and the neighbors
	// from 'other' are not acyclic, skip this cube
	if (!otheracyclic)
		return false;

	// if there are neighbors from 'cset' then check if the neighbors
	// from both 'cset' and 'other' taken together form an acyclic set
	if ((ncset + nother > 1) && ((ncset + nother == maxneighbors) ||
		!acyclic (dim, *b)))
	{
		return false;
	}
	return true;
} /* acyclic_rel */


// --------------------------------------------------
// ------------------ reduce cubes ------------------
// --------------------------------------------------

/// Computes the image of the face under the combinatorial cubical
/// multivalued map, but doesn't take the given cube into consideration.
/// Returns the number of cubes whose images were added to 'img'.
template <class tCube, class tCell>
int_t computeimage (hashedset<tCube> &img, const tCell &face,
	const mvmap<tCube,tCube> &map, const hashedset<tCube> &cset,
	const tCube &ignore)
{
	// get the coordinates of the cubical cell
	typename tCell::CoordType left [tCell::MaxDim];
	face. leftcoord (left);
	typename tCell::CoordType right [tCell::MaxDim];
	face. rightcoord (right);

	// find the images of all the cubes containing this cell
	int spacedim = face. spacedim ();
	typename tCell::CoordType leftb [tCell::MaxDim];
	typename tCell::CoordType rightb [tCell::MaxDim];
	for (int j = 0; j < spacedim; ++ j)
	{
		typename tCell::CoordType diff =
			(left [j] == right [j]) ? 1 : 0;
		leftb [j] = (left [j] - diff);
		rightb [j] = (right [j] + diff);
	}
	tRectangle<typename tCell::CoordType> r (leftb, rightb, spacedim);
	const typename tCell::CoordType *c;
	int_t countimages = 0;
	while ((c = r. get ()) != NULL)
	{
		if (!tCube::PointBase::check (c, spacedim))
			continue;
		tCube q (c, spacedim);
		if (q == ignore)
			continue;
		if (!cset. check (q))
			continue;
		img. add (map (q));
		++ countimages;
	}

	return countimages;
} /* computeimage */

/// Verifies if the map remains acyclic after the addition or removal of the
/// given cube to/from the union of the first and the second set.
/// Assumes that the map is acyclic before the change.
/// Returns 'true' if yes for sure, 'false' if there is some doubt about it.
template <class tCube>
bool remainsacyclic (const mvmap<tCube,tCube> &map, const tCube &q,
	const hashedset<tCube> &cset1, const hashedset<tCube> *cset2 = 0)
{
	// compute the maximal number of neighbors of a cube
	int_t maxneighbors = getmaxneighbors (q. dim ());

	// prepare a bitfield and allocate it if necessary
	static BitField b;
	static int_t _maxneighbors = 0;
	if (maxneighbors != _maxneighbors)
	{
		if (_maxneighbors > 0)
			b. free ();
		_maxneighbors = maxneighbors;
		b. allocate (maxneighbors);
	}

	// clear the neighborbits
	b. clearall (maxneighbors);

	// get the bitfield representing the set of the neighbors of the cube
	if (cset2)
		getneighbors (q, &b, makesetunion (cset1, *cset2), 0);
	else
		getneighbors (q, &b, cset1, 0);

	// create all the faces of the cube
	gcomplex<typename tCube::CellType,integer> faces;
	addneighbors (q, b, faces);
	faces. addboundaries ();

	// compute the new images of all the faces
	// and determine if they are acyclic
	int startdim = faces. dim ();
	for (int d = startdim; d >= 0; -- d)
	{
		for (int_t i = 0; i < faces [d]. size (); ++ i)
		{
			// compute the image of the face in the first set
			hashedset<tCube> img;
			int_t n = computeimage (img, faces [d] [i], map,
				cset1, q);

			// add the image of the second set if applicable
			if (cset2)
			{
				n += computeimage (img, faces [d] [i], map,
					*cset2, q);
			}

			// if this is the image of only one cube, it is Ok
			if (n == 1)
				continue;

			// verify whether the large image (with 'q')
			// can be reduced towards the small one (without 'q')
			hashedset<tCube> imgsurplus = map (q);
			imgsurplus. remove (img);
			cubreducequiet (img, imgsurplus);
			if (!imgsurplus. empty ())
				return false;
		}
	}

	return true;
} /* remainsacyclic */

/// A small helper function which adds neighbors of the given cube
/// to the given set. All the neighbors of 'q' which appear in 'cubset'
/// are added to the set 'neighbors' using the 'getneighbors' function
/// if BDDs are in use. Otherwise, it is assumed that all the neighbors
/// of 'q' are already in the set 'neighbors'.
/// Then all the neighbors which are not in the 'notthese' set
/// are added to the queue.
template <class tCube, class tCubeSet>
inline void addcubeneighbors (const tCube &q, int dim,
	const tCubeSet &cubset, bitfield *b, hashedset<tCube> &neighbors,
	hashedset<tCube> &queue, const hashedset<tCube> &notthese)
{
	// determine the neighbors of this cube (if not done yet)
	if (dim <= MaxBddDim)
		getneighbors (q, b, cubset, &neighbors, 0);

	// add the computed neighbors of this cube to the queue
	for (int_t j = 0; j < neighbors. size (); ++ j)
	{
		if (!notthese. check (neighbors [j]))
			queue. add (neighbors [j]);
	}

	return;
} /* addcubeneighbors */

/// Reduce the set 'cset' towards 'maincset'. These sets must be disjoint.
/// If 'quiet' is set to true, then suppresses any messages.
/// Returns the number of cubes removed from 'cset'.
template <class tCube>
int_t cubreducequiet (const hashedset<tCube> &maincset, hashedset<tCube> &cset,
	bool quiet = true)
{
	// remember the initial number of cubes in the set to be reduced
	int_t prev = cset. size ();

	// if the case is trivial, return the answer
	if (!prev)
		return 0;

	// determine the space dimension
	int dim = cset [0]. dim ();

	// compute the maximal number of neighbors of a cube
	int_t maxneighbors = getmaxneighbors (dim);

	// prepare a bitfield and allocate it if necessary
	static BitField b;
	static int_t _maxneighbors = 0;
	if (maxneighbors != _maxneighbors)
	{
		if (_maxneighbors > 0)
			b. free ();
		_maxneighbors = maxneighbors;
		b. allocate (maxneighbors);
	}

	// prepare a queue for cubes to check
	hashedset<tCube> queue;

	// prepare a counter for displaying the progress of computations
	int_t count = 0;

	// remove cubes which can be removed
	// and add their neighbors to the queue
	for (int_t i = 0; i < cset. size (); ++ i)
	{
		// show progress indicator
		++ count;
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";

		// clear the neighborbits
		b. clearall (maxneighbors);

		// prepare a set for storing the neighbors of the cube
		hashedset<tCube> neighbors;

		// if the neighborhood of the cube is not acyclic, skip it
		if (!acyclic (cset [i], dim, makesetunion (maincset, cset),
			&b, maxneighbors, &neighbors))
		{
			continue;
		}

		// remove this cube from the queue
		queue. remove (cset [i]);

		// determine the neighbors of this cube (if not done yet)
		// and add the computed neighbors of this cube to the queue
		addcubeneighbors (cset [i], dim, cset, &b, neighbors,
			queue, maincset);

		// remove this cube from 'cset'
		if (!quiet)
			sseq << '0' << cset [i] << '\n';
		cset. removenum (i);
		-- i;
	}

	// add a temporary progress indicator and reset the counter
	if (!quiet)
		scon << "*";
	count = 0;

	// take cubes from the queue and remove them if possible
	while (!queue. empty ())
	{
		// update the progress indicator
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
		++ count;

		// take a cube from the queue
		tCube c = queue [0];
		queue. removenum (0);

		// clear the neighborbits
		b. clearall (maxneighbors);

		// prepare a set for storing the neighbors of the cube
		hashedset<tCube> neighbors;

		// if the neighborhood of the cube is not acyclic, skip it
		if (!acyclic (c, dim, makesetunion (maincset, cset),
			&b, maxneighbors, &neighbors))
		{
			continue;
		}

		// determine the neighbors of this cube (if not done yet)
		// and add the computed neighbors of this cube to the queue
		addcubeneighbors (c, dim, cset, &b, neighbors,
			queue, maincset);

		// remove the cube from 'cset'
		if (!quiet)
			sseq << '0' << c << '\n';
		cset. remove (c);
	}

	// erase the temporary progress indicator
	if (!quiet)
		scon << "\b \b";

	// return the number of cubes removed from 'added'
	return prev - cset. size ();
} /* cubreducequiet */

// ??? - this description seems to be wrong!
/// Reduces a pair of sets of cubes for relative homology computation.
/// Returns the number of cubes removed from both sets.
template <class tCube>
inline int_t cubreduce (const hashedset<tCube> &maincset,
	hashedset<tCube> &cset)
{
	return cubreducequiet (maincset, cset, false);
} /* cubreduce */

/// Reduces a pair of sets of cubes for relative homology computation.
/// Does not remove any cubes from the set 'keep'. Additionally makes sure
/// that the acyclicity of the given map is preserved.
/// If 'quiet' is set to true then suppresses any messages.
/// Returns the number of cubes removed from both sets.
template <class tCube>
int_t cubreducequiet (hashedset<tCube> &cset, hashedset<tCube> &other,
	mvmap<tCube,tCube> &map, const hashedset<tCube> &keep,
	bool quiet = true)
{
	// determine if the acyclicity of the map should be considered
	bool checkacyclic = !map. getdomain (). empty ();

	// remember the initial number of cubes in both sets
	int_t prev = cset. size () + other. size ();

	// if the case is trivial, return the answer
	if (cset. empty ())
	{
		if (!other. empty ())
		{
			hashedset<tCube> empty;
			other = empty;
		}
		return prev;
	}

	// determine the space dimension
	int dim = cset [0]. dim ();

	// compute the maximal number of neighbors of a cube
	int_t maxneighbors = getmaxneighbors (dim);

	// prepare a bitfield and allocate it if necessary
	static BitField b;
	static int_t _maxneighbors = 0;
	if (maxneighbors != _maxneighbors)
	{
		if (_maxneighbors > 0)
			b. free ();
		_maxneighbors = maxneighbors;
		b. allocate (maxneighbors);
	}

	// prepare a queue for cubes to check
	hashedset<tCube> queue;

	// prepare a counter for displaying the progress of computations
	int_t count = 0;

	// go through the other set, remove cubes which can be removed,
	// and add their neighbors to the queue
	for (int_t i = 0; i < other. size (); ++ i)
	{
		// show the progress indicator
		++ count;
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";

		// if the cube should be kept, skip it
		if (keep. check (other [i]))
			continue;

		// clear the neighborbits
		b. clearall (maxneighbors);

		// prepare a set for storing the neighbors of the cube
		hashedset<tCube> neighbors, *none = 0;

		// if the cube cannot be removed, skip it
		if (!acyclic_rel (other [i], dim, cset, other, &b,
			maxneighbors, none, &neighbors))
		{
			continue;
		}

		// make sure that the acyclicity of the map on A is OK
		if (checkacyclic && !remainsacyclic (map, other [i], other))
			continue;

		// make sure that the acyclicity of the map on X is OK
		if (checkacyclic && !remainsacyclic (map, other [i],
			other, &cset))
			continue;

		// remove this cube from the queue
		queue. remove (other [i]);

		// determine the neighbors of this cube (if not done yet)
		// and add the computed neighbors of this cube to the queue
		addcubeneighbors (other [i], dim, other, &b, neighbors,
			queue, keep);

		// remove this cube from 'other'
		if (!quiet)
			sseq << '0' << other [i] << '\n';
		other. removenum (i);
		-- i;
	}

	// show a temporary progress indicator and reset the counter
	if (!quiet)
		scon << '.';
	count = 0;

	// go through the main set, remove cubes which can be removed,
	// and add their neighbors to the queue
	for (int_t i = 0; i < cset. size (); ++ i)
	{
		// show progress indicator
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
		++ count;

		// if this cube should be kept, skip it
		if (keep. check (cset [i]))
			continue;

		// clear the neighborbits
		b. clearall (maxneighbors);

		// prepare a set for storing the neighbors of the cube
		hashedset<tCube> neighbors;

		// if the neighborhood of the cube is not acyclic, skip it
		if (!acyclic (cset [i], dim, makesetunion (cset, other),
			&b, maxneighbors, &neighbors))
		{
			continue;
		}

		// make sure that the acyclicity of the map on X is OK
		if (checkacyclic && !remainsacyclic (map, cset [i],
			cset, &other))
		{
			continue;
		}

		// remove this cube from the queue
		queue. remove (cset [i]);

		// determine the neighbors of this cube (if not done yet)
		// and add the computed neighbors of this cube to the queue
		addcubeneighbors (cset [i], dim, makesetunion (cset, other),
			&b, neighbors, queue, keep);

		// remove this cube from 'cset'
		if (!quiet)
			sseq << '0' << cset [i] << '\n';
		cset. removenum (i);
		-- i;
	}

	// update the temporary progress indicator and reset the counter
	if (!quiet)
		scon << "\b*";
	count = 0;

	// take cubes from the queue and remove them if possible
	while (!queue. empty ())
	{
		// update the progress indicator
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
		++ count;

		// take a cube from the queue and remove it from the queue
		tCube c = queue [0];
		queue. removenum (0);

		// clean the neighborbits
		b. clearall (maxneighbors);

		// if this cube belongs to the other set...
		if (other. check (c))
		{
			// prepare a set for storing the neighbors
			hashedset<tCube> neighbors;

			if (!acyclic_rel (c, dim, cset, other, &b,
				maxneighbors, &cset, &other))
			{
				continue;
			}

			// make sure that the map's acyclicity on A is OK
			if (checkacyclic && !remainsacyclic (map, c, other))
				continue;

			// make sure that the map's acyclicity on X is OK
			if (checkacyclic && !remainsacyclic (map, c,
				other, &cset))
				continue;

			// determine the neighbors of this cube (if not yet)
			// and add the computed neighbors to the queue
			addcubeneighbors (c, dim, makesetunion (cset, other),
				&b, neighbors, queue, keep);

			// remove the cube from the other set
			if (!quiet)
				sseq << '0' << c << '\n';
			other. remove (c);
		}

		// otherwise, if this cube belongs to 'cset'...
		else
		{
			// prepare a set for storing the neighbors
			hashedset<tCube> neighbors;

			// if the neighborhood of the cube is not acyclic
			// then skip it
			if (!acyclic (c, dim, makesetunion (cset, other),
				&b, maxneighbors, &neighbors))
			{
				continue;
			}

			// make sure that the acyclicity of the map on X is OK
			if (checkacyclic && !remainsacyclic (map, c,
				cset, &other))
			{
				continue;
			}

			// determine the neighbors of this cube (if not yet)
			// and add the computed neighbors to the queue
			addcubeneighbors (c, dim, makesetunion (cset, other),
				&b, neighbors, queue, keep);

			// remove the cube from 'cset'
			if (!quiet)
				sseq << '0' << c << '\n';
			cset. remove (c);
		}
	}

	// erase the temporary progress indicator
	if (!quiet)
		scon << "\b \b";

	// return the number of cubes removed from both sets
	return prev - cset. size () - other. size ();
} /* cubreducequiet */

/// Reduces a pair of sets of cubes for relative homology computation.
/// Does not remove any cubes from the set 'keep'. Additionally makes sure
/// that the acyclicity of the given map is preserved.
/// Returns the number of cubes removed from both sets.
template <class tCube>
inline int_t cubreduce (hashedset<tCube> &cset, hashedset<tCube> &other,
	mvmap<tCube,tCube> &cubmap, const hashedset<tCube> &keep)
{
	return cubreducequiet (cset, other, cubmap, keep, false);
} /* cubreduce */

/// Reduces a pair of sets of cubes for relative homology computation.
/// Does not remove any cubes from the set 'keep'.
/// If 'quiet' is set to true, then suppresses any messages.
/// Returns the number of cubes removed from both sets.
template <class tCube>
inline int_t cubreducequiet (hashedset<tCube> &cset, hashedset<tCube> &other,
	const hashedset<tCube> &keep, bool quiet = true)
{
	mvmap<tCube,tCube> emptymap;
	return cubreducequiet (cset, other, emptymap, keep, quiet);
} /* cubreducequiet */

/// Reduces a pair of sets of cubes for relative homology computation.
/// Does not remove any cubes from the set 'keep'.
/// Returns the number of cubes removed from both sets.
template <class tCube>
inline int_t cubreduce (hashedset<tCube> &cset, hashedset<tCube> &other,
	const hashedset<tCube> &keep)
{
	return cubreducequiet (cset, other, keep, false);
} /* cubreduce */


// --------------------------------------------------
// ------------------ expand cubes ------------------
// --------------------------------------------------

/// Expands the set 'other' towards 'cset' without changing the homology
/// of (cset + other, other). The two sets must be disjoint.
template <class tCube>
int_t cubexpand (hashedset<tCube> &cset, hashedset<tCube> &other,
	bool quiet = false)
{
	// if the case is trivial, return the answer
	if (cset. empty () || other. empty ())
		return 0;

	// remember the initial number of cubes in the main set
	int_t prev = cset. size ();

	// determine the dimension of the cubes
	int dim = cset [0]. dim ();

	// compute the maximal number of neighbors of a cube
	int_t maxneighbors = getmaxneighbors (dim);

	// prepare a bitfield and allocate it if necessary
	static BitField b;
	static int_t _maxneighbors = 0;
	if (maxneighbors != _maxneighbors)
	{
		if (_maxneighbors > 0)
			b. free ();
		_maxneighbors = maxneighbors;
		b. allocate (maxneighbors);
	}

	// prepare a queue for cubes to check
	hashedset<tCube> queue;

	// prepare a counter for displaying the progress of computations
	int_t count = 0;

	// go through the main set, move cubes to the other set
	// if possible, and add their neighbors to the queue
	for (int_t i = 0; i < cset. size (); ++ i)
	{
		// show progress indicator if suitable
		++ count;
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";

		// clear the neighborbits
		b. clearall (maxneighbors);

		// if the neighborhood of the cube is not acyclic, skip it
		if (!acyclic (cset [i], dim, other, &b, maxneighbors))
			continue;
		
		// remove this cube from the queue
		queue. remove (cset [i]);

		// add neighbors from 'cset' to the queue
		b. clearall (maxneighbors);
		getneighbors (cset [i], &b, cset, &queue, 0);

		// move the cube to the other set
		if (!quiet)
			sseq << '2' << cset [i] << '\n';
		other. add (cset [i]);
		cset. removenum (i);
		-- i;
	}

	// show a temporary progress indicator and reset the counter
	if (!quiet)
		scon << '*';
	count = 0;

	// take cubes from the queue and move them from 'cset' to 'other'
	while (queue. size ())
	{
		// show progress indicator
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
		++ count;

		// take a cube from the queue
		const tCube c = queue [0];
		queue. removenum (0);

		// clear the neighborbits
		b. clearall (maxneighbors);

		// if the neighborhood of the cube is not acyclic, skip it
		if (!acyclic (c, dim, other, &b, maxneighbors))
			continue;

		// add the neighbors from 'cset' to the queue
		b. clearall (maxneighbors);
		getneighbors (c, &b, cset, &queue, 0);

		// move this cube from 'cset' to 'other'
		if (!quiet)
			sseq << '2' << c << '\n';
		cset. remove (c);
		other. add (c);
	}

	// erase the temporary progress indicator
	if (!quiet)
		scon << "\b \b";

	// return the number of cubes removed from 'cset'
	return prev - cset. size ();
} /* cubexpand */

/// Expands the set 'other' towards 'cset' without changing the homology
/// of (cset + other, other). The two sets must be disjoint.
/// Increases 'img' if necessary to cover F (other),
/// but moves cubes only if it can prove that the inclusion of the old 'img'
/// into the new, enlarged 'img' induces an isomorphism in homology.
/// Every cube added to 'img' is removed from 'imgsrc'.
template <class tCube>
int_t cubexpand (hashedset<tCube> &cset, hashedset<tCube> &other,
	hashedset<tCube> &imgsrc, hashedset<tCube> &img,
	const mvmap<tCube,tCube> &map, bool indexmap,
	bool checkacyclic, bool quiet = false)
{
	// if the case is trivial, return the answer
	if (cset. empty () || other. empty ())
		return 0;

	// remember the initial number of cubes in the main set
	int_t prev = cset. size ();

	// determine the space dimension
	int dim = cset [0]. dim ();

	// compute the maximal number of neighbors of a cube
	int_t maxneighbors = getmaxneighbors (dim);

	// prepare a bitfield and allocate it if necessary
	static BitField b;
	static int_t _maxneighbors = 0;
	if (maxneighbors != _maxneighbors)
	{
		if (_maxneighbors > 0)
			b. free ();
		_maxneighbors = maxneighbors;
		b. allocate (maxneighbors);
	}

	// prepare a queue for cubes to check
	hashedset<tCube> queue;

	// prepare a counter for displaying the progress of computations
	int_t count = 0;

	// go through the main set, move cubes to the other set
	// if possible, and add their neighbors to the queue
	for (int_t i = 0; i < cset. size (); ++ i)
	{
		// show progress indicator
		++ count;
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";

		// take a cube from 'cset'
		const tCube &c = cset [i];

		// clear the neighborbits
		b. clearall (maxneighbors);

		// if the neighborhood of the cube is not acyclic, skip it
		if (!acyclic (c, dim, other, &b, maxneighbors))
			continue;
		
		// take the image and reduce what is outside 'img'
		const hashedset<tCube> &cubimage = map (c);
		hashedset<tCube> ximage = cubimage;
		if (indexmap)
			ximage. add (c);
		ximage. remove (img);
		cubreducequiet (img, ximage);

		// if the image could not be reduced, skip the cube
		if (!ximage. empty ())
			continue;

		// make sure that the acyclicity of the map is not spoiled
		if (checkacyclic && !remainsacyclic (map, c, other))
			continue;

		// add the image of this cube to the image of the map
		if (!quiet && !cubimage. empty ())
		{
			sseq << "R\n";
			for (int_t j = 0; j < cubimage. size (); ++ j)
				sseq << '2' << cubimage [j] << '\n';
			if (indexmap)
				sseq << '2' << c << '\n';
		}
		img. add (cubimage);
		if (indexmap)
			img. add (c);

		// remove from 'imgsrc' all the cubes added to 'img'
		imgsrc. remove (cubimage);
		if (indexmap)
			imgsrc. remove (c);

		// remove this cube from the queue
		queue. remove (c);

		// add neighbors from 'cset' to the queue
		b. clearall (maxneighbors);
		getneighbors (c, &b, cset, &queue, 0);

		// move the cube to the other set
		if (!quiet)
			sseq << "L\n" << '2' << c << '\n';
		other. add (c);
		cset. removenum (i);
		-- i;
	}

	// show a temporary progress indicator and reset the counter
	if (!quiet)
		scon << '*';
	count = 0;

	// take cubes from the queue and move them from 'cset' to 'other'
	while (!queue. empty ())
	{
		// show progress indicator
		if (!quiet && !(count % 373))
			scon << std::setw (10) << count <<
				"\b\b\b\b\b\b\b\b\b\b";
		++ count;

		// take a cube from the queue
		tCube c = queue [0];
		queue. removenum (0);

		// clear the neighborbits
		b. clearall (maxneighbors);

		// if the neighborhood of the cube is not acyclic, skip it
		if (!acyclic (c, dim, other, &b, maxneighbors))
			continue;
		
		// take the image and reduce what is outside 'img'
		const hashedset<tCube> &cubimage = map (c);
		hashedset<tCube> ximage = cubimage;
		if (indexmap)
			ximage. add (c);
		ximage. remove (img);
		cubreducequiet (img, ximage);

		// if the image could not be reduced, skip the cube
		if (!ximage. empty ())
			continue;

		// make sure that the acyclicity of the map is not spoiled
		if (checkacyclic && !remainsacyclic (map, c, other))
			continue;

		// add the image of this cube to the image of the map
		if (!quiet && !cubimage. empty ())
		{
			sseq << "R\n";
			for (int_t i = 0; i < cubimage. size (); ++ i)
				sseq << '2' << cubimage [i] << '\n';
			if (indexmap)
				sseq << '2' << c << '\n';
		}
		img. add (cubimage);
		if (indexmap)
			img. add (c);

		// remove from 'imgsrc' all the cubes added to 'img'
		imgsrc. remove (cubimage);
		if (indexmap)
			imgsrc. remove (c);

		// add the neighbors from 'cset' to the queue
		b. clearall (maxneighbors);
		getneighbors (c, &b, cset, &queue, 0);

		// move this cube from 'cset' to 'other'
		if (!quiet)
			sseq << "L\n" << '2' << c << '\n';
		cset. remove (c);
		other. add (c);
	}

	// erase the temporary progress indicator
	if (!quiet)
		scon << "\b \b";

	// return the number of cubes removed from 'cset'
	return prev - cset. size ();
} /* cubexpand */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CUBISETS_H_ 

/// @}

