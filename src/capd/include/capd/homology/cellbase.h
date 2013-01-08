/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cellbase.h
///
/// This file contains the definition of cubical cells which use
/// a cube base class for indexing all the possible coordinate
/// combinations. This saves a lot of memory if the same points
/// are reused, e.g., as vertices of adjacent cubical cells.
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


#ifndef _CAPD_HOMOLOGY_CELLBASE_H_ 
#define _CAPD_HOMOLOGY_CELLBASE_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/chains.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/gcomplex.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cubebase.h"
#include "capd/homology/cellmain.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// ----------- CubicalCell with PointBase -----------
// --------------------------------------------------

/// This class defines cubical cell in R^n with edges parallel to the axes
/// and with size 0 or 1 in each direction.
/// This implementation uses a PointBase class to index all the
/// vertices of cells which appear in the program.
template <class coordtype>
class tCellBase
{
public:
	/// The type of the coordinates.
	typedef coordtype CoordType;

	/// The maximal dimension of a cell.
	static const int MaxDim = tCubeBase<coordtype>::MaxDim;

	/// The maximal dimension of the embedding space of a cell.
	static const int MaxSpaceDim = tCubeBase<coordtype>::MaxDim;

	/// The point base (for wrapping and tabulating coordinates).
	typedef typename tCubeBase<coordtype>::PointBase PointBase;

	/// The constructor of an empty cubical cell.
	tCellBase ();

	/// The constructor of a cell spanning from one point to another.
	tCellBase (const coordtype *c1, const coordtype *c2,
		int spcdim, int celldim = -1);

	/// The constructor of a cell as an intersection of two full cubes.
	tCellBase (const tCubeBase<coordtype> &q1,
		const tCubeBase<coordtype> &q2);

	/// The constructor of an arbitrary k-dimensional face
	/// of a full cube.
	tCellBase (const tCubeBase<coordtype> &q, int facedim);

	/// The constructor of a full-dimensional cubical cell.
	explicit tCellBase (const tCubeBase<coordtype> &q);

	/// The constructor of a projection of a cell to the given number
	/// of coordinates that start at the given offset.
	tCellBase (const tCellBase<coordtype> &q, int offset, int ncoords);

	/// The copy constructor.
	tCellBase (const tCellBase<coordtype> &c);

	/// The assignment operator.
	tCellBase<coordtype> &operator =
		(const tCellBase<coordtype> &c);

	/// Returns the dimension of the cubical cell.
	int dim () const;

	/// Returns the dimension of the embedding space.
	int spacedim () const;

	/// Fills in the given table with the left corner coordinates.
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
	friend inline int operator == (const tCellBase<coordtype> &c1,
		const tCellBase<coordtype> &c2)
	{
		return (c1. n1 == c2. n1) && (c1. n2 == c2. n2);
	} /* operator == */

private:
	/// Returns the first number of the cubical cell vertices.
	int_t num1 () const;

	/// Returns the second number of the cubical cell vertices.
	int_t num2 () const;

	/// The left vertex: high 6 bits = space dim, the remaining bits
	/// form the number of the point in an appropriate pointset.
	int_t n1;

	/// The right vertex: high 6 bits = cube dim, the remaining bits
	/// form the number of the point in an appropriate pointset.
	int_t n2;

	/// Initializes a new cell given its two corners.
	void initialize (const coordtype *c1, const coordtype *c2,
		int spcdim, int celldim = -1);

}; /* class tCellBase */

// --------------------------------------------------

template<class coordtype>
int tCellBase<coordtype>::OutputBits = 0;

// --------------------------------------------------

template <class coordtype>
inline int_t tCellBase<coordtype>::num1 () const
{
	return (n1 & NumMask);
} /* tCellBase::num1 */

template <class coordtype>
inline int_t tCellBase<coordtype>::num2 () const
{
	return (n2 & NumMask);
} /* tCellBase::num2 */

template <class coordtype>
inline void tCellBase<coordtype>::initialize (const coordtype *c1,
	const coordtype *c2, int spcdim, int celldim)
{
	// test the validity of the dimension
	if (spcdim <= 0)
		throw "Non-positive dimension of the space.";
	else if (spcdim >= MaxDim)
		throw "Too high dimension of a cell.";

	// get the number of the left vertex
	n1 = PointBase::number (c1, spcdim);
	if (n1 < 0)
		throw "Negative number of the left vertex.";

	// get the number of the right vertex
	n2 = PointBase::number (c2, spcdim);
	if (n2 < 0)
		throw "Negative number of the right vertex.";

	// calculate the dimension of the cubical cell if it is unknown
	if (celldim < 0)
	{
		celldim = 0;
		c1 = PointBase::coord (n1, spcdim);
		c2 = PointBase::coord (n2, spcdim);
		for (int i = 0; i < spcdim; ++ i)
		{
			if (c2 [i] != c1 [i])
				++ celldim;
		}
	}

	// add the space dimension and the cell dimension to the numbers
	n1 |= (static_cast<int_t> (spcdim) << NumBits);
	n2 |= (static_cast<int_t> (celldim) << NumBits);
	return;
} /* tCellBase::initialize */

// --------------------------------------------------

template <class coordtype>
inline tCellBase<coordtype>::tCellBase ()
: n1 (0), n2 (0)
{
	return;
} /* tCellBase::tCellBase */

template <class coordtype>
inline tCellBase<coordtype>::tCellBase
	(const coordtype *c1, const coordtype *c2, int spcdim, int celldim)
{
	initialize (c1, c2, spcdim, celldim);
	return;
} /* tCellBase::tCellBase */

template <class coordtype>
inline tCellBase<coordtype>::tCellBase
	(const tCubeBase<coordtype> &q1, const tCubeBase<coordtype> &q2)
{
	// get the dimension of the space and check for consistency
	int spcdim = q1. dim ();
	if (spcdim != q2. dim ())
		throw "Trying to intersect cubes of different dimension.";

	// get the coordinates of minimal vertices of both cubes
	coordtype c1 [MaxDim];
	q1. coord (c1);
	coordtype c2 [MaxDim];
	q2. coord (c2);

	// prepare tables for the new coordinates of the cubical cell
	coordtype left [MaxDim];
	coordtype right [MaxDim];

	// compute the new coordinates of the cubical cell
	int celldim = CommonCell (left, right, c1, c2, spcdim,
		PointBase::getwrapping (spcdim));
	
	// create the cell as computed
	initialize (left, right, spcdim, celldim);

	return;
} /* tCellBase::tCellBase */

template <class coordtype>
inline tCellBase<coordtype>::tCellBase (const tCubeBase<coordtype> &q,
	int facedim)
: n1 (q. n)
{
	// check the dimensions
	int spcdim = static_cast<int> (n1 >> NumBits);
	if (facedim < 0)
		throw "Negative dimension of a face requested.";
	if (facedim > spcdim)
		throw "Too high dimension of a face requested.";

	// create the opposite corner of the cell
	const coordtype *c1 = PointBase::coord (num1 (), spcdim);
	coordtype c2 [MaxDim];
	for (int i = 0; i < spcdim; ++ i)
		c2 [i] = c1 [i] + ((i < facedim) ? 1 : 0);

	// determine the number of the opposite corner and add cell dimension
	n2 = PointBase::number (c2, spcdim) |
		(static_cast<int_t> (facedim) << NumBits);
	return;
} /* tCellBase::tCellBase */

template <class coordtype>
inline tCellBase<coordtype>::tCellBase (const tCubeBase<coordtype> &q)
: n1 (q. n)
{
	// create the opposite corner of the cell
	int spcdim = static_cast<int> (n1 >> NumBits);
	const coordtype *c1 = PointBase::coord (num1 (), spcdim);
	coordtype c2 [MaxDim];
	for (int i = 0; i < spcdim; ++ i)
		c2 [i] = c1 [i] + 1;

	// determine the number of the opposite corner and add cell dimension
	n2 = PointBase::number (c2, spcdim) |
		(static_cast<int_t> (spcdim) << NumBits);
	return;
} /* tCellBase::tCellBase */

template <class coordtype>
inline tCellBase<coordtype>::tCellBase (const tCellBase<coordtype> &q,
	int offset, int ncoords)
{
	int spcdim = static_cast<int> (q. n1 >> NumBits);
	if ((offset < 0) || (ncoords <= 0) || (offset + ncoords > spcdim))
		throw "Wrong cell projection requested.";
	const coordtype *c1 = PointBase::coord (q. n1 & NumMask, spcdim);
	const coordtype *c2 = PointBase::coord (q. n2 & NumMask, spcdim);
	initialize (c1 + offset, c2 + offset, ncoords);
	return;
} /* tCellBase::tCellBase */

template <class coordtype>
inline tCellBase<coordtype>::tCellBase (const tCellBase<coordtype> &q)
: n1 (q. n1), n2 (q. n2)
{
	return;
} /* tCellBase::tCellBase */

template <class coordtype>
inline tCellBase<coordtype> &tCellBase<coordtype>::operator =
	(const tCellBase<coordtype> &q)
{
	n1 = q. n1;
	n2 = q. n2;
	return *this;
} /* tCellBase::operator = */

template <class coordtype>
inline int tCellBase<coordtype>::dim () const
{
	return static_cast<int> (n2 >> NumBits);
} /* tCellBase::dim */

template <class coordtype>
inline int tCellBase<coordtype>::spacedim () const
{
	return (n1 >> NumBits);
} /* tCellBase::spacedim */

template <class coordtype>
inline coordtype *tCellBase<coordtype>::leftcoord (coordtype *c) const
{
	const coordtype *leftc = PointBase::coord (num1 (), spacedim ());
	if (!c)
		throw "Null pointer to save left coordinates.";
	copycoord (c, leftc, spacedim ());
	return c;
} /* tCellBase::leftcoord */

template <class coordtype>
inline coordtype *tCellBase<coordtype>::rightcoord (coordtype *c) const
{
	const coordtype *rightc = PointBase::coord (num2 (), spacedim ());
	if (!c)
		throw "Null pointer to save right coordinates.";
	copycoord (c, rightc, spacedim ());
	return c;
} /* tCellBase::rightcoord */

template <class coordtype>
inline int_t tCellBase<coordtype>::hashkey1 () const
{
	return ((n1 ^ 0x55555555u) << 17) ^ ((n1 ^ 0xAAAAAAAAu) << 7) ^
		((n2 ^ 0xAAAAAAAAu) >> 7);
} /* tCellBase::hashkey1 */

template <class coordtype>
inline int_t tCellBase<coordtype>::hashkey2 () const
{
	return ((n2 ^ 0xAAAAAAAAu) << 21) ^ ((n2 ^ 0x55555555u) << 10) ^
		((n1 ^ 0x55555555u) >> 9);
} /* tCellBase::hashkey2 */

template <class coordtype>
const char *tCellBase<coordtype>::name ()
{
	return "cubical cell";
} /* tCellBase::name */

template <class coordtype>
const char *tCellBase<coordtype>::pluralname ()
{
	return "cubical cells";
} /* tCellBase::pluralname */

// --------------------------------------------------

/// Checks if the two cells are different.
template <class coordtype>
inline int operator != (const tCellBase<coordtype> &c1,
	const tCellBase<coordtype> &c2)
{
	return !(c1 == c2);
} /* operator != */

// --------------------------------------------------

/// Computes the Cartesian product of two cells.
template <class coordtype>
inline tCellBase<coordtype> operator *
	(const tCellBase<coordtype> &c1,
	const tCellBase<coordtype> &c2)
{
	// get the underlying space dimensions for both cells
	int d1 = c1. spacedim (), d2 = c2. spacedim ();
	if (d1 + d2 >= tCellBase<coordtype>::MaxDim)
		throw "Too high dimension of a Cartesian product of cells.";

	// prepare arrays for the coordinates of the cell to create
	coordtype left [tCellBase<coordtype>::MaxDim];
	coordtype right [tCellBase<coordtype>::MaxDim];

	// extract the coordinates of the first cell
	c1. leftcoord (left);
	c1. rightcoord (right);

	// extract the coordinates of the second cell
	c2. leftcoord (left + d1);
	c2. rightcoord (right + d1);

	// create the Cartesian product of the cells
	return tCellBase<coordtype> (left, right, d1 + d2,
		c1. dim () + c2. dim ());
} /* operator * */

/// Writes a cell to an output stream.
template <class coordtype>
inline std::ostream &operator << (std::ostream &out,
	const tCellBase<coordtype> &c)
{
	return WriteCubicalCell (out, c);
} /* operator << */

/// Reads a cell from an input stream.
template <class coordtype>
inline std::istream &operator >> (std::istream &in,
	tCellBase<coordtype> &c)
{
	return ReadCubicalCell (in, c);
} /* operator >> */

// --------------------------------------------------

/// Computes the i-th boundary element of a cell.
/// If only existing cells are considered,
/// returns '*this' if the requested boundary cell doesn't exist.
template <class coordtype>
inline tCellBase<coordtype> boundarycell (const tCellBase<coordtype> &q,
	int i, bool onlyexisting)
{
	return CubicalBoundaryCell (q, i, onlyexisting);
} /* boundarycell */

/// Computes the i-th boundary element of a cell.
template <class coordtype>
inline tCellBase<coordtype> boundarycell (const tCellBase<coordtype> &q,
	int i)
{
	return CubicalBoundaryCell (q, i);
} /* boundarycell */
	
/// Returns the length of the boundary of a cell.
template <class coordtype>
inline int boundarylength (const tCellBase<coordtype> &q)
{
	return CubicalBoundaryLength (q);
} /* boundarylength */

/// Returns the i-th coefficient in the boundary of a cell.
template <class coordtype>
inline int boundarycoef (const tCellBase<coordtype> &q, int i)
{
	return CubicalBoundaryCoef (q, i);
} /* boundarycoef */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CELLBASE_H_ 

/// @}

