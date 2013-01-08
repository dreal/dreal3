/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cellvar.h
///
/// This file defines cubical cells whose embedding space dimension
/// is not known apriori and therefore the array of coordinates is allocated
/// each time a cubical cell is created.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: August 4, 2010.


#ifndef _CAPD_HOMOLOGY_CELLVAR_H_ 
#define _CAPD_HOMOLOGY_CELLVAR_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/chains.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/gcomplex.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cubevar.h"
#include "capd/homology/cellmain.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------- CubicalCell with allocated memory --------
// --------------------------------------------------

/// This class defines cubical cell in R^n with edges parallel to the axes
/// and with size 0 or 1 in each direction.
/// In this implementation, an array is allocated for the coordinates
/// of the minimal vertex of a cell.
template <class coordtype>
class tCellVar
{
public:
	/// The type of the coordinates.
	typedef coordtype CoordType;

	/// The maximal dimension of a cell.
	static const int MaxDim = // MaxBasDim;
		(tCubeVar<coordtype>::MaxDim < MaxBasDim) ?
		tCubeVar<coordtype>::MaxDim : MaxBasDim;

	/// The maximal dimension of the embedding space of a cell.
	static const int MaxSpaceDim = tCubeVar<coordtype>::MaxDim;

	/// The point base (for wrapping and tabulating coordinates).
	typedef typename tCubeVar<coordtype>::PointBase PointBase;

	/// The constructor of an empty cubical cell.
	tCellVar ();

	/// The constructor of a cell spanning from one point to another.
	tCellVar (const coordtype *c1, const coordtype *c2,
		int spcdim, int celldim = -1);

	/// The constructor of a cell as an intersection of two cubes.
	tCellVar (const tCubeVar<coordtype> &q1,
		const tCubeVar<coordtype> &q2);

	/// The constructor of an arbitrary k-dimensional face
	/// of a full cube.
	tCellVar (const tCubeVar<coordtype> &q, int facedim);

	/// The constructor of a full-dimensional cubical cell.
	explicit tCellVar (const tCubeVar<coordtype> &q);

	/// The constructor of a projection of a cell to the given number
	/// of coordinates that start at the given offset.
	tCellVar (const tCellVar<coordtype> &q, int offset, int ncoords);

	/// The copy constructor.
	tCellVar (const tCellVar<coordtype> &c);

	/// The assignment operator.
	tCellVar<coordtype> &operator = (const tCellVar<coordtype> &c);

	/// Returns the dimension of the cubical cell.
	int dim () const;

	/// Returns the dimension of the embedding space of the cubical cell.
	int spacedim () const;

	/// Fills in the given table with the right corner coordinates.
	coordtype *leftcoord (coordtype *c) const;

	/// Fills in the given table with the right corner coordinates.
	coordtype *rightcoord (coordtype *c) const;

	/// Returns hashing key no. 1 required by the hashing set template.
	int_t hashkey1 () const;

	/// Return shashing key no. 2 required by the hashing set template.
	int_t hashkey2 () const;

	/// Returns the name of the objects represented by this class.
	static const char *name ();

	/// Returns the plural name of the objects represented by this class.
	static const char *pluralname ();

	/// Bit masks that define how to output the cell. If 'BitProduct'
	/// is set, then the cell is displayed as a Cartesian product of
	/// intervals. Otherwise, it is indicated by two opposite vertices.
	/// If 'BitSpace' is set, the space is inserted in the output.
	enum OutputBitValues
	{
		BitProduct = 0x01,	// unset => two vertices
		BitSpace = 0x02
	};

	/// The output bits which determine how a cell is written.
	static int OutputBits;

	// --- friends: ---

	/// Verifies if two cells are identical.
	friend inline int operator == (const tCellVar<coordtype> &c1,
		const tCellVar<coordtype> &c2)
	{
		return ((c1. n == c2. n) && ((c1. n == 0) ||
			thesame (c1. tab, c2. tab, c1. spacedim ())));
	} /* operator == */

private:
	/// The lower left etc. corner of the cell.
	coordtype *tab;

	/// High 6 bits = the dimension of the space.
	/// Remaining bits set to 1 iff the cell has width 1
	/// in the specified direction.
	int_t n;

	/// Initializes a new cell given its two corners.
	void initialize (const coordtype *c1, const coordtype *c2,
		int spcdim, int celldim = -1);

}; /* class tCellVar */

// --------------------------------------------------

template<class coordtype>
int tCellVar<coordtype>::OutputBits = 0;

// --------------------------------------------------

template <class coordtype>
inline void tCellVar<coordtype>::initialize (const coordtype *c1,
	const coordtype *c2, int spcdim, int)
{
	// test the validity of the dimension
	if (spcdim <= 0)
		throw "Non-positive dimension of the space.";
	else if (spcdim >= MaxDim)
		throw "Too high dimension of a cell.";

	// initialize the internal number with the space dimension
	n = static_cast<int_t> (spcdim) << NumBits;

	// prepare a table for coordinates if necessary
	tab = new coordtype [spcdim];
	if (!tab)
		throw "Not enough memory to create a cell.";

	// copy the left corner coordinates to the cell
	PointBase::wrapcopy (tab, c1, spcdim);

	// prepare wrapped right coordinates for the detection of cell bits
	coordtype r [MaxDim];
	PointBase::wrapcopy (r, c2, spcdim);

	// set the bits of the cell
	for (int i = 0; i < spcdim; ++ i)
	{
		if (tab [i] != r [i])
			n |= (static_cast<int_t> (1) << i);
	}
	return;
} /* tCellVar::initialize */

template <class coordtype>
inline tCellVar<coordtype>::tCellVar ()
: tab (0), n (0)
{
	return;
} /* tCellVar::tCellVar */

template <class coordtype>
inline tCellVar<coordtype>::tCellVar
	(const coordtype *c1, const coordtype *c2, int spcdim, int celldim)
{
	initialize (c1, c2, spcdim, celldim);
	return;
} /* tCellVar::tCellVar */

template <class coordtype>
inline int tCellVar<coordtype>::dim () const
{
	int count = 0;
	for (int i = 0; i < NumBits; ++ i)
	{
		if (n & (static_cast<int_t> (1) << i))
			++ count;
	}
	return count;
} /* tCellVar::dim */

template <class coordtype>
inline int tCellVar<coordtype>::spacedim () const
{
	return static_cast<int> (n >> NumBits);
} /* tCellVar::spacedim */

template <class coordtype>
inline tCellVar<coordtype>::tCellVar (const tCellVar<coordtype> &q,
	int offset, int ncoords)
{
	int spcdim = static_cast<int> (q. n >> NumBits);
	if ((offset < 0) || (ncoords <= 0) || (offset + ncoords > spcdim))
		throw "Wrong cell projection requested.";
	coordtype right [MaxDim];
	q. rightcoord (right);
	initialize (q. tab + offset, right + offset, ncoords);
//	*** More efficient [unfinished, yet] ***
//	tab = new coordtype [spcdim];
//	if (!tab)
//		throw "Not enough memory to create a projected cell.";
//	for (int i = 0; i < spcdim; ++ i)
//		tab [i] = q. tab [i];
//	[...]
	return;
} /* tCellVar::tCellVar */

template <class coordtype>
inline tCellVar<coordtype>::tCellVar (const tCellVar<coordtype> &q)
{
	n = q. n;
	tab = new coordtype [spacedim ()];
	if (!tab)
		throw "Not enough memory to copy a cubical cell.";
	copycoord (tab, q. tab, spacedim ());
	return;
} /* tCellVar::tCellVar */

template <class coordtype>
inline tCellVar<coordtype> &tCellVar<coordtype>::operator =
	(const tCellVar<coordtype> &q)
{
	// determine the new dimension
	int d = q. spacedim ();

	// allocate a new table if the dimension is to be changed
	if (d != spacedim ())
	{
		if (tab)
			delete [] tab;
		tab = new coordtype [d];
		if (!tab)
			throw "Not enough memory to copy a cubical cell.";
	}

	// copy the data of the cubical cell
	copycoord (tab, q. tab, d);
	n = q. n;

	return *this;
} /* tCellVar::operator = */

template <class coordtype>
inline coordtype *tCellVar<coordtype>::leftcoord (coordtype *c) const
{
	if (!c)
		throw "Null pointer to save left coordinates.";
	int d = spacedim ();
	for (int i = 0; i < d; ++ i)
		c [i] = tab [i];
	return c;
} /* tCellVar::leftcoord */

template <class coordtype>
inline coordtype *tCellVar<coordtype>::rightcoord (coordtype *c) const
{
	if (!c)
		throw "Null pointer to save right coordinates.";
	int d = spacedim ();
	for (int i = 0; i < d; ++ i)
	{
		c [i] = tab [i];
		if (n & (static_cast<int_t> (1) << i))
			++ (c [i]);
	}
	PointBase::wrapcoord (c, d);
	return c;
} /* tCellVar::rightcoord */

template <class coordtype>
inline int_t tCellVar<coordtype>::hashkey1 () const
{
	switch (spacedim ())
	{
	case 0:
		return 0;
	case 1:
		return (static_cast<int_t> (tab [0]) << 12) ^ n;
	case 2:
		return (((static_cast<int_t> (tab [0])) << 18) +
			((static_cast<int_t> (tab [1])) << 6)) ^ n;
	default:
		return (((static_cast<int_t> (tab [0])) << 18) +
			((static_cast<int_t> (tab [1])) << 6) +
			((static_cast<int_t> (tab [2])) >> 6)) ^ n;
	}
} /* tCellVar::hashkey1 */

template <class coordtype>
inline int_t tCellVar<coordtype>::hashkey2 () const
{
	int d = spacedim ();
	switch (d)
	{
	case 0:
		return 0;
	case 1:
		return (static_cast<int_t> (tab [0]) << 3) ^ (n << 5);
	case 2:
		return ((static_cast<int_t> (tab [0]) >> 1) +
			(static_cast<int_t> (tab [1]) << 13)) ^ (n << 5);
	default:
		return (((static_cast<int_t> (tab [d - 1])) << 20) +
			((static_cast<int_t> (tab [d - 2])) << 9) +
			((static_cast<int_t> (tab [d - 3])) >> 1)) ^
			(n << 5);
	}
} /* tCellVar::hashkey2 */

template <class coordtype>
const char *tCellVar<coordtype>::name ()
{
	return "cubical cell";
} /* tCellVar::name */

template <class coordtype>
const char *tCellVar<coordtype>::pluralname ()
{
	return "cubical cells";
} /* tCellVar::pluralname */

// --------------------------------------------------

template <class coordtype>
inline tCellVar<coordtype>::tCellVar
	(const tCubeVar<coordtype> &q1, const tCubeVar<coordtype> &q2)
{
	// prepare tables for coordinates of the cubical cell
	coordtype left [MaxDim];
	coordtype right [MaxDim];

	// get the coordinates of minimal vertices of both cubes
	coordtype c1 [MaxDim];
	q1. coord (c1);
	coordtype c2 [MaxDim];
	q2. coord (c2);

	// get the dimension of the space and check for consistency
	int spcdim = q1. dim ();
	if (spcdim != q2. dim ())
		throw "Trying to intersect cubes of different dimension.";

	// calculate the coordinates of both vertices of the cubical cell
	// and the dimension of the cubical cell
	int celldim = 0;
	const coordtype *wrap = PointBase::getwrapping (spcdim);
	for (int i = 0; i < spcdim; ++ i)
	{
		if (c1 [i] == c2 [i])
		{
			left [i] = c1 [i];
			right [i] = c1 [i];
			++ right [i];
			++ celldim;
		}
		else if ((c1 [i] - c2 [i] == -1) || (wrap && wrap [i] &&
			(c1 [i] - c2 [i] == wrap [i] - 1)))
		{
			left [i] = c2 [i];
			right [i] = c2 [i];
		}
		else if ((c1 [i] - c2 [i] == 1) || (wrap && wrap [i] &&
			(c1 [i] - c2 [i] == -wrap [i] + 1)))
		{
			left [i] = c1 [i];
			right [i] = c1 [i];
		}
		else
			throw "The cubes do not intersect.";
	}

	// initialize the data of the cube
	initialize (left, right, spcdim, celldim);

	return;
} /* tCellVar::tCellVar */

template <class coordtype>
inline tCellVar<coordtype>::tCellVar (const tCubeVar<coordtype> &q)
// NOTE: This function is not as efficient as it could be. Instead of using
// the "initialize" function, it should create the data structures itself.
{
	// get the coordinates of minimal vertex of the cube
	const coordtype *left = q. tab + 1;

	// get the dimension of the space and of the cell
	int d = q. dim ();

	// prepare a table for coordinates of the other vertex of the cell
	coordtype right [MaxDim];

	// calculate the coordinates of other vertex of the cell
	for (int i = 0; i < d; ++ i)
		right [i] = left [i] + 1;

	// initialize the cell
	initialize (left, right, d, d);
	return;
} /* tCellVar::tCellVar */

template <class coordtype>
inline tCellVar<coordtype>::tCellVar (const tCubeVar<coordtype> &q,
	int facedim)
// NOTE: This function is not as efficient as it could be. Instead of using
// the "initialize" function, it should create the data structures itself.
{
	// get the coordinates of minimal vertex of the cube
	const coordtype *left = q. tab + 1;

	// prepare a table for coordinates of the other vertex of the cell
	coordtype right [MaxDim];

	// get the dimension of the space and of the cell
	int d = q. dim ();

	// calculate the coordinates of other vertex of the cell
	for (int i = 0; i < d; ++ i)
		right [i] = left [i] + ((i < facedim) ? 1 : 0);

	// initialize the cell
	initialize (left, right, d, facedim);
	return;
} /* tCellVar::tCellVar */

// --------------------------------------------------

/// Checks if the two cells are different.
template <class coordtype>
inline int operator != (const tCellVar<coordtype> &c1,
	const tCellVar<coordtype> &c2)
{
	return !(c1 == c2);
} /* operator != */

// --------------------------------------------------

/// Computes the Cartesian product of two cells.
template <class coordtype>
inline tCellVar<coordtype> operator *
	(const tCellVar<coordtype> &c1,
	const tCellVar<coordtype> &c2)
{
	// get the underlying space dimensions for both cells
	int d1 = c1. spacedim (), d2 = c2. spacedim ();
	if (d1 + d2 >= tCellVar<coordtype>::MaxDim)
		throw "Too high dimension of a Cartesian product of cells.";

	// prepare arrays for the coordinates of the cell to create
	coordtype left [tCellVar<coordtype>::MaxDim];
	coordtype right [tCellVar<coordtype>::MaxDim];

	// extract the coordinates of the first cell
	c1. leftcoord (left);
	c1. rightcoord (right);

	// extract the coordinates of the second cell
	c2. leftcoord (left + d1);
	c2. rightcoord (right + d1);

	// create the Cartesian product of the cells
	return tCellVar<coordtype> (left, right, d1 + d2,
		c1. dim () + c2. dim ());
} /* operator * */

/// Writes a cell to an output stream.
template <class coordtype>
inline std::ostream &operator << (std::ostream &out,
	const tCellVar<coordtype> &c)
{
	return WriteCubicalCell (out, c);
} /* operator << */

/// Reads a cell from an input stream.
template <class coordtype>
inline std::istream &operator >> (std::istream &in,
	tCellVar<coordtype> &c)
{
	return ReadCubicalCell (in, c);
} /* operator >> */

// --------------------------------------------------

/// Computes the i-th boundary element of a cell.
template <class coordtype>
inline tCellVar<coordtype> boundarycell (const tCellVar<coordtype> &q,
	int i, bool onlyexisting)
{
	return CubicalBoundaryCell (q, i, onlyexisting);
} /* boundarycell */

/// Computes the i-th boundary element of a cell.
template <class coordtype>
inline tCellVar<coordtype> boundarycell (const tCellVar<coordtype> &q,
	int i)
{
	return CubicalBoundaryCell (q, i);
} /* boundarycell */
	
/// Returns the length of the boundary of a cell.
template <class coordtype>
inline int boundarylength (const tCellVar<coordtype> &q)
{
	return CubicalBoundaryLength (q);
} /* boundarylength */

/// Returns the i-th coefficient in the boundary of a cell.
template <class coordtype>
inline int boundarycoef (const tCellVar<coordtype> &q, int i)
{
	return CubicalBoundaryCoef (q, i);
} /* boundarycoef */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CELLVAR_H_ 

/// @}

