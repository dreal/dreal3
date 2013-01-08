/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file neighbor.h
///
/// This file contains various procedures relating to neighborhoods
/// of cubes in full cubical sets.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: October 25, 2008.


#ifndef _CAPD_HOMOLOGY_NEIGHBOR_H_ 
#define _CAPD_HOMOLOGY_NEIGHBOR_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cube.h"
#include "capd/homology/cell.h"
#include "capd/homology/cubacycl.h"
#include "capd/homology/tabulate.h"
#include "capd/homology/known.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {

// --------------------------------------------------
// ----------------- max neighbors ------------------
// --------------------------------------------------

/// Returns the maximal number of neighbors of a cube: 3^dim - 1.
inline int_t getmaxneighbors (int dim)
{
	if (dim < 0)
		return 0;
	const int maxdim = 17;
	const int neighbors [maxdim] = {0, 2, 8, 26, 80, 242, 728,
		2186, 6560, 19682, 59048, 177146, 531440, 1594322,
		4782968, 14348906, 43046720};
	if (dim < maxdim)
		return neighbors [dim];
	int_t ncount = neighbors [maxdim - 1] + 1;
	for (int i = maxdim - 1; i < dim; ++ i)
		ncount *= 3;
	return (ncount - 1);
} /* getmaxneighbors */


// --------------------------------------------------
// ----------------- neighbor bits ------------------
// --------------------------------------------------

/// Returns the number of the neighbor bit for the given neighbor of 'q'
/// or -1 if not a neighbor or the same cube as 'q'.
template <class tCube>
int_t neighbor2bit (const tCube &q, const tCube &neighbor)
{
	// define the type of coordinates
	typedef typename tCube::CoordType coordType;

	coordType c0 [tCube::MaxDim];
	q. coord (c0);
	coordType c1 [tCube::MaxDim];
	neighbor. coord (c1);
	int dim = q. dim ();

	int_t number = 0;
	const coordType *wrap = tCube::PointBase::getwrapping (dim);
	for (int i = 0; i < dim; ++ i)
	{
		if (i)
			number *= 3;
		switch (c1 [i] - c0 [i])
		{
			case -1:
				++ number;
			case 1:
				++ number;
				break;
			case 0:
				break;
			default:
				if (!wrap || !wrap [i])
					return -1;
				if ((c1 [i] - c0 [i]) == (wrap [i] - 1))
					number += 2;
				else if ((c1 [i] - c0 [i]) == (1 - wrap [i]))
					++ number;
				else
					return -1;
				break;
		}
	}

	return number - 1;
} /* neighbor2bit */

/// Returns the number of the neighbor bit for the neighbor which intersects
/// the given cube at the face provided.
template <class tCube>
int_t neighbor2bit (const tCube &q, const typename tCube::CellType &face)
{
	// define the type of coordinates
	typedef typename tCube::CoordType coordType;

	// determine the space dimension and the coordinates of the input
	int dim = q. dim ();
	coordType coord [tCube::MaxDim];
	q. coord (coord);
	coordType cLeft [tCube::MaxDim];
	face. leftcoord (cLeft);
	coordType cRight [tCube::MaxDim];
	face. rightcoord (cRight);

	// compute the number of the neighbor based on the coordinates
	int_t number = 0;
	for (int i = 0; i < dim; ++ i)
	{
		if (i)
			number *= 3;
		// if the neighbor is shifted upwards
		if (cLeft [i] != coord [i])
			number += 1;
		// if the neighbor is shifted downwards
		else if (cRight [i] == cLeft [i])
			number += 2;
		// otherwise the neighbor is at the same level
	}

	return number - 1;
} /* neighbor2bit */

/// Creates the neighbor of the given cube with the specified number.
/// If the coordinates of the neighbor do not belong to 'PointBase',
/// then returns 'q', unless 'unconditional' is set to true.
template <class tCube>
tCube bit2neighbor (const tCube &q, int_t number, bool unconditional = false)
{
	// define the type of coordinates
	typedef typename tCube::CoordType coordType;

	coordType c0 [tCube::MaxDim];
	q. coord (c0);
	coordType c1 [tCube::MaxDim];
	int dim = q. dim ();

	++ number;
	for (int i = dim - 1; i >= 0; -- i)
	{
		switch (number % 3)
		{
			case 2:
				c1 [i] = c0 [i] - 1;
				break;
			case 1:
				c1 [i] = c0 [i] + 1;
				break;
			case 0:
				c1 [i] = c0 [i];
				break;
			default:
				throw "Erratic neighbor.";
		}
		number /= 3;
	}

	if (unconditional || tCube::PointBase::check (c1, dim))
		return tCube (c1, dim);
	else
		return q;
} /* bit2neighbor */


// --------------------------------------------------
// ----------------- get neighbors ------------------
// --------------------------------------------------

/// Gets neighbors of the given cube from the given set and indicates them
/// in the bit field provided. Returns the number of neighbors.
/// If the limit is nonzero then quits after having found
/// that many neighbors. Scans through the entire set of cubes.
template <class tCube, class tCubeSet1, class tCubeSet2>
int_t getneighbors_scan (const tCube &q, BitField *bits,
	const tCubeSet1 &theset, tCubeSet2 *neighbors, int_t limit)
{
	// prepare a counter for the number of neighbors
	int_t count = 0;

	// go through all the elements in the set
	for (int_t i = 0; i < theset. size (); ++ i)
	{
		// if this is the current cube, ignore it
		if (theset [i] == q)
			continue;

		// determine the number of this neighbor
		int_t number = neighbor2bit (q, theset [i]);

		// if not neighbor, ignore it
		if (number < 0)
			continue;

		// set the corresponding bit in the bit field
		if (bits)
			bits -> set (number);

		// add the cube to the set of neighbors
		if (neighbors)
			neighbors -> add (theset [i]);

		// increase the counter
		++ count;

		// if this is enough then finish
		if (limit && (count >= limit))
			return count;
	}

	return count;
} /* getneighbors_scan */

/// Gets neighbors of the given cube from the given set and indicates them
/// in the bit field provided. Returns the number of neighbors.
/// If the limit is nonzero then quits after having found
/// that many neighbors. Generates all the possible neighbors.
template <class tCube, class tCubeSet1, class tCubeSet2>
int_t getneighbors_generate (const tCube &q, BitField *bits,
	const tCubeSet1 &theset, tCubeSet2 *neighbors, int_t limit)
{
	// determine the upper bound for the number of neighbors
	int_t maxneighbors = getmaxneighbors (q. dim ());

	// prepare a counter for the number of neighbors
	int_t count = 0;

	// go through all possible neighbor numbers
	for (int_t number = 0; number < maxneighbors; ++ number)
	{
		// create a neighbor cube
		tCube neighbor = bit2neighbor (q, number);

		// if the neighbor doesn't exist, ignore it
		if (neighbor == q)
			continue;

		// if this cube is not in the set, ignore it
		if (!theset. check (neighbor))
			continue;

		// set the appropriate bit in the bit field
		if (bits)
			bits -> set (number);

		// add the cube to the set of neighbors
		if (neighbors)
			neighbors -> add (neighbor);

		// increase the counter
		++ count;

		// if this is enough then finish
		if (limit && (count >= limit))
			return count;
	}

	return count;
} /* getneighbors_generate */

/// Gets neighbors of the given cube from the given set and indicates them
/// in the bit field provided. Returns the number of neighbors.
/// If the limit is nonzero then quits after having found
/// that many neighbors.
template <class tCube, class tCubeSet1, class tCubeSet2>
int_t getneighbors (const tCube &q, BitField *bits,
	const tCubeSet1 &theset, tCubeSet2 *neighbors, int_t limit)
{
	// if the answer is trivial, return it
	if (theset. empty ())
		return 0;

	// if the set is small
	if (theset. size () < getmaxneighbors (q. dim ()))
	{
		return getneighbors_scan (q, bits, theset, neighbors, limit);
	}
	else
	{
		return getneighbors_generate (q, bits, theset, neighbors,
			limit);
	}
} /* getneighbors */

// Gets neighbors of the given cube from the given set and indicates them
// in the bit field provided. Returns the number of neighbors.
// If the limit is nonzero then quits after having found
// that many neighbors.
template <class tCube, class tCubeSet>
int_t getneighbors (const tCube &q, BitField *bits,
	const tCubeSet &theset, int_t limit)
{
	hashedset<typename tCubeSet::value_type> *none = 0;
	return getneighbors (q, bits, theset, none, limit);
} /* getneighbors */


// --------------------------------------------------
// ----------------- add neighbors ------------------
// --------------------------------------------------

/// Adds neighbors listed in the given bit field to the set of cubes
/// unless they are in the 'forbidden' set.
/// Returns the number of added neighbors.
template <class tCube, class tCubeSet>
int_t addneighbors (const tCube &q, const BitField &bits, tCubeSet &set,
	const tCubeSet &notthese)
{
	int_t maxneighbors = getmaxneighbors (q. dim ());

	int_t count = 0;
	int_t number = bits. find (0, maxneighbors);
	while (number >= 0)
	{
		tCube neighbor = bit2neighbor (q, number);
		if (!notthese. check (neighbor))
			set. add (neighbor);
		number = bits. find (number + 1, maxneighbors);
		++ count;
	}

	return count;
} /* addneighbors */

/// Adds neighbors listed in the given bit field to the set of cubes.
/// If not 'unconditional', then adds only cubes which already exist.
template <class tCube, class tCubeSet>
int_t addneighbors (const tCube &q, const BitField &bits, tCubeSet &set,
	bool unconditional = false)
{
	int_t maxneighbors = getmaxneighbors (q. dim ());
	int_t count = 0;

	int_t number = bits. find (0, maxneighbors);
	while (number >= 0)
	{
		tCube neighbor = bit2neighbor (q, number, unconditional);
		set. add (neighbor);
		number = bits. find (number + 1, maxneighbors);
		++ count;
	}

	return count;
} /* addneighbors */

/// Adds intersections of neighbors listed in the given bit field with the
/// given cube to the cubical complex.
/// If not 'unconditional', then adds only cubes which already exist.
template <class tCube, class tCell>
int_t addneighbors (const tCube &q, const BitField &bits,
	gcomplex<tCell,integer> &c, bool unconditional = false)
{
	// define the type of coordinates
	typedef typename tCube::CoordType coordType;

	// determine the space dimension
	int dim = q. dim ();

	// compute the maximal number of neighbors
	int_t maxneighbors = getmaxneighbors (dim);

	// extract the coordinates of the central cube
	coordType coord [tCube::MaxDim];
	q. coord (coord);

	// prepare arrays for the coordinates of boundary cells
	coordType cLeft [tCube::MaxDim];
	coordType cRight [tCube::MaxDim];

	// prepare a counter of boundary cells
	int_t count = 0;

	// find the first neighbor number
	int_t number = bits. find (0, maxneighbors);

	// process all the neighbor numbers
	while (number >= 0)
	{
		// prepare the coordinates of the boundary cell
		int_t n = number + 1;
		for (int i = dim - 1; i >= 0; -- i)
		{
			switch (n % 3)
			{
				case 2:
					cLeft [i] = coord [i];
					cRight [i] = coord [i];
					break;
				case 1:
					cLeft [i] = coord [i] + 1;
					cRight [i] = coord [i] + 1;
					break;
				case 0:
					cLeft [i] = coord [i];
					cRight [i] = coord [i] + 1;
					break;
			}
			n /= 3;
		}

		// add the cell to the complex of boundary cells
		c. add (tCell (cLeft, cRight, dim));

		// increase the counter of boundary cells
		++ count;

		// take the next neighbor number
		number = bits. find (number + 1, maxneighbors);
	}

	return count;
} /* addneighbors */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_NEIGHBOR_H_ 

/// @}

