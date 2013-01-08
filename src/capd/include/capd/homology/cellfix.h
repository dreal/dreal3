/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cellfix.h
///
/// This class defines cubical cells in which the embedding space dimension
/// is known apriori. Since this dimension is used as a template parameter,
/// this approach saves a lot of memory allocation and deallocation,
/// since arrays of fixed length are used.
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


#ifndef _CAPD_HOMOLOGY_CELLFIX_H_ 
#define _CAPD_HOMOLOGY_CELLFIX_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/chains.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/gcomplex.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cubefix.h"
#include "capd/homology/cellmain.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// ----------- CubicalCell with fixed dim -----------
// --------------------------------------------------

/// This class defines cubical cell in R^n with edges parallel to the axes
/// and with size 0 or 1 in each direction.
/// This implementation assumes that the embedding space dimension is known
/// at time of compilation.
template <int dimfix, class coordtype>
class tCellFix
{
public:
	/// The type of the coordinates.
	typedef coordtype CoordType;

	/// The maximal dimension of a cell.
	static const int MaxDim =
		(tCubeFix<dimfix,coordtype>::MaxDim < MaxBasDim) ?
		tCubeFix<dimfix,coordtype>::MaxDim : MaxBasDim;

	/// The maximal dimension of the embedding space of a cell.
	static const int MaxSpaceDim = dimfix;

	/// The point base (for wrapping and tabulating coordinates).
	typedef typename tCubeFix<dimfix,coordtype>::PointBase PointBase;

	/// The constructor of an empty cubical cell.
	tCellFix ();
	
	/// The constructor of a cell spanning from one point to another.
	tCellFix (const coordtype *c1, const coordtype *c2,
		int spcdim = 0, int celldim = -1);

	/// The constructor of a cell as an intersection of two cubes.
	tCellFix (const tCubeFix<dimfix,coordtype> &q1,
		const tCubeFix<dimfix,coordtype> &q2);

	/// The constructor of an arbitrary k-dimensional face
	/// of a full cube.
	tCellFix (const tCubeFix<dimfix,coordtype> &q, int facedim);

	/// The constructor of a full-dimensional cubical cell.
	explicit tCellFix (const tCubeFix<dimfix,coordtype> &q);

	/// The constructor of a projection of a cell to the given number
	/// of coordinates that start at the given offset.
	template <int dimhigh>
	tCellFix (const tCellFix<dimhigh,coordtype> &q,
		int offset, int ncoords);

	/// The copy constructor.
	tCellFix (const tCellFix<dimfix,coordtype> &c);

	/// The assignment operator.
	tCellFix<dimfix,coordtype> &operator =
		(const tCellFix<dimfix,coordtype> &c);

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

	/// Returns hashing key no. 2 required by the hashing set template.
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
	template <int _dimfix, class _coordtype>
	friend inline int operator ==
		(const tCellFix<_dimfix,_coordtype> &c1,
		const tCellFix<_dimfix,_coordtype> &c2)
	{
		return ((c1. n == c2. n) && (!memcmp (c1. tab, c2. tab,
			dimfix * sizeof (coordtype))));
	} /* operator == */

private:
	/// A table with the left coordinate of the cell.
	coordtype tab [dimfix];

	/// High 6 bits = the dimension of the cell (not: space).
	/// Remaining bits set to 1 iff the cell has width 1
	/// in the specified direction.
	int_t n;

	/// Initializes a new cell, given its two corners.
	void initialize (const coordtype *c1, const coordtype *c2,
		int celldim = -1);

}; /* class tCellFix */

// --------------------------------------------------

template <int dimfix, class coordtype>
int tCellFix<dimfix,coordtype>::OutputBits = 0;

// --------------------------------------------------

template <int dimfix, class coordtype>
inline void tCellFix<dimfix,coordtype>::initialize (const coordtype *c1,
	const coordtype *c2, int celldim)
{
	// copy the left corner coordinates to the cell
	PointBase::wrapcopy (tab, c1, dimfix);

	// prepare wrapped right coordinates for the detection of cell bits
	coordtype r [dimfix];
	PointBase::wrapcopy (r, c2, dimfix);

	// if the dimension of the cell is known, then compute the bits only
	if (celldim >= 0)
	{
		n = static_cast<int_t> (celldim) << NumBits;
		if (!celldim)
			return;
		for (int i = 0; i < dimfix; ++ i)
		{
			if (tab [i] != r [i])
				n |= (static_cast<int_t> (1) << i);
		}
		return;
	}

	// set the bits of the cell and compute its actual dimension
	n = 0;
	int dim = 0;
	for (int i = 0; i < dimfix; ++ i)
	{
		if (tab [i] != r [i])
		{
			n |= (static_cast<int_t> (1) << i);
			++ dim;
		}
	}
	n |= static_cast<int_t> (dim) << NumBits;

	return;
} /* tCellFix::initialize */

// --------------------------------------------------

template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype>::tCellFix ()
:n (0)
{
	if (dimfix > MaxDim)
		throw "Too high fixed-dim cell dimension.";
	return;
} /* tCellFix::tCellFix */

template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype>::tCellFix
	(const coordtype *c1, const coordtype *c2, int spcdim, int celldim)
{
	// test the validity of the dimension
	if (spcdim < 0)
		throw "Negative dimension of the space.";
	else if ((spcdim > 0) && (spcdim != dimfix))
		throw "Wrong dimension of a cell.";
	if (dimfix > MaxDim)
		throw "Too high fixed-dim cell dimension.";

	// initialize the cell
	initialize (c1, c2, celldim);
	return;
} /* tCellFix::tCellFix */
	
template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype>::tCellFix
	(const tCubeFix<dimfix,coordtype> &q1,
	const tCubeFix<dimfix,coordtype> &q2)
{
	if (dimfix > MaxDim)
		throw "Too high fixed-dim cell dimension.";

	// get the coordinates of minimal vertices of both cubes
	coordtype c1 [dimfix];
	q1. coord (c1);
	coordtype c2 [dimfix];
	q2. coord (c2);

	// prepare tables for the new coordinates of the cubical cell
	coordinate left [dimfix];
	coordinate right [dimfix];

	// compute the new coordinates of the cubical cell
	int celldim = CommonCell (left, right, c1, c2, dimfix,
		PointBase::getwrapping (dimfix));
	
	// create the cell as computed
	initialize (left, right, celldim);

	return;
} /* tCellFix::tCellFix */

template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype>::tCellFix
	(const tCubeFix<dimfix,coordtype> &q, int facedim)
{
	if (facedim < 0)
		throw "Negative dimension of a face requested.";
	if (facedim > dimfix)
		throw "Too high dimension of a face requested.";
	if (dimfix > MaxDim)
		throw "Too high fixed-dim cell dimension.";
	copycoord (tab, q. tab, dimfix);
	n = static_cast<int_t> (facedim) << NumBits;
	for (int i = 0; i < facedim; ++ i)
		n |= static_cast<int_t> (1) << i;
	return;
} /* tCellFix::tCellFix */

template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype>::tCellFix
	(const tCubeFix<dimfix,coordtype> &q)
: n ((static_cast<int_t> (dimfix) << NumBits) | NumMask)
{
	if (dimfix > MaxDim)
		throw "Too high fixed-dim cell dimension.";
	copycoord (tab, q. tab, dimfix);
	return;
} /* tCellFix::tCellFix */

template <int dimfix, class coordtype>
template <int dimhigh>
inline tCellFix<dimfix,coordtype>::tCellFix
	(const tCellFix<dimhigh,coordtype> &q, int offset, int ncoords)
{
	if ((offset < 0) || (ncoords <= 0) || (ncoords != dimfix) ||
		(offset + ncoords > dimhigh))
		throw "Wrong cell projection requested.";
	// note: the following can be done in a slightly more efficient way,
	// without creating the right coordinates and calling "initialize"
	coordtype right [dimhigh];
	q. rightcoord (right);
	initialize (q. tab + offset, right + offset);
	return;
} /* tCellFix::tCellFix */

template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype>::tCellFix
	(const tCellFix<dimfix,coordtype> &q)
: n (q. n)
{
	copycoord (tab, q. tab, dimfix);
	return;
} /* tCellFix::tCellFix */

template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype> &tCellFix<dimfix,coordtype>::operator =
	(const tCellFix<dimfix,coordtype> &q)
{
	memcpy (tab, q. tab, dimfix * sizeof (coordtype));
	n = q. n;
	return *this;
} /* tCellFix::operator = */

template <int dimfix, class coordtype>
inline int tCellFix<dimfix,coordtype>::dim () const
{
	return static_cast<int> (n >> NumBits);
} /* tCellFix::dim */

template <int dimfix, class coordtype>
inline int tCellFix<dimfix,coordtype>::spacedim () const
{
	return dimfix;
} /* tCellFix::spacedim */

template <int dimfix, class coordtype>
inline coordtype *tCellFix<dimfix,coordtype>::leftcoord (coordtype *c) const
{
	if (!c)
		throw "Null pointer to save left coordinates.";
	for (int i = 0; i < dimfix; ++ i)
		c [i] = tab [i];
	return c;
} /* tCellFix::leftcoord */

template <int dimfix, class coordtype>
inline coordtype *tCellFix<dimfix,coordtype>::rightcoord (coordtype *c) const
{
	if (!c)
		throw "Null pointer to save right coordinates.";
	for (int i = 0; i < dimfix; ++ i)
	{
		c [i] = tab [i] +
			((n & (static_cast<int_t> (1) << i)) ? 1 : 0);
	}
	PointBase::wrapcoord (c, spacedim ());
	return c;
} /* tCellFix::rightcoord */

template <int dimfix, class coordtype>
inline int_t tCellFix<dimfix,coordtype>::hashkey1 () const
{
	switch (dimfix)
	{
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
} /* tCellFix::hashkey1 */

template <int dimfix, class coordtype>
inline int_t tCellFix<dimfix,coordtype>::hashkey2 () const
{
	switch (dimfix)
	{
	case 1:
		return (static_cast<int_t> (tab [0]) << 3) ^ (n << 5);
	case 2:
		return ((static_cast<int_t> (tab [0]) >> 1) +
			(static_cast<int_t> (tab [1]) << 13)) ^ (n << 5);
	default:
		return (((static_cast<int_t> (tab [dimfix - 1])) << 20) +
			((static_cast<int_t> (tab [dimfix - 2])) << 9) +
			((static_cast<int_t> (tab [dimfix - 3])) >> 1)) ^
			(n << 5);
	}
} /* tCellFix::hashkey2 */

template <int dimfix, class coordtype>
const char *tCellFix<dimfix,coordtype>::name ()
{
	return "cubical cell";
} /* tCellFix::name */

template <int dimfix, class coordtype>
const char *tCellFix<dimfix,coordtype>::pluralname ()
{
	return "cubical cells";
} /* tCellFix::pluralname */

// --------------------------------------------------

/// Checks if the two cells are different.
template <int dimfix, class coordtype>
inline int operator != (const tCellFix<dimfix,coordtype> &c1,
	const tCellFix<dimfix,coordtype> &c2)
{
	return !(c1 == c2);
} /* operator != */

// --------------------------------------------------

/// Computes the Cartesian product of two cells.
template <int dim1, int dim2, class coordtype>
inline tCellFix<dim1+dim2,coordtype> operator *
	(const tCellFix<dim1,coordtype> &c1,
	const tCellFix<dim2,coordtype> &c2)
{
	// prepare arrays for the coordinates of the cell to create
	coordtype left [dim1 + dim2];
	coordtype right [dim1 + dim2];

	// extract the coordinates of the first cell
	c1. leftcoord (left);
	c1. rightcoord (right);

	// extract the coordinates of the second cell
	c2. leftcoord (left + dim1);
	c2. rightcoord (right + dim1);

	// create the Cartesian product of the cells
	return tCellFix<dim1+dim2,coordtype> (left, right,
		dim1 + dim2, c1. dim () + c2. dim ());
} /* operator * */

/// Writes a cell to an output stream.
template <int dimfix, class coordtype>
inline std::ostream &operator << (std::ostream &out,
	const tCellFix<dimfix,coordtype> &c)
{
	return WriteCubicalCell (out, c);
} /* operator << */

/// Reads a cell from an input stream.
template <int dimfix, class coordtype>
inline std::istream &operator >> (std::istream &in,
	tCellFix<dimfix,coordtype> &c)
{
	return ReadCubicalCell (in, c);
} /* operator >> */

// --------------------------------------------------

/// Computes the i-th boundary element of a cell.
template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype> boundarycell
	(const tCellFix<dimfix,coordtype> &q, int i, bool onlyexisting)
{
	return CubicalBoundaryCell (q, i, onlyexisting);
} /* boundarycell */

/// Computes the i-th boundary element of a cell.
template <int dimfix, class coordtype>
inline tCellFix<dimfix,coordtype> boundarycell
	(const tCellFix<dimfix,coordtype> &q, int i)
{
	return CubicalBoundaryCell (q, i);
} /* boundarycell */
	
/// Returns the length of the boundary of a cell.
template <int dimfix, class coordtype>
inline int boundarylength (const tCellFix<dimfix,coordtype> &q)
{
	return CubicalBoundaryLength (q);
} /* boundarylength */

/// Returns the i-th coefficient in the boundary of a cell.
template <int dimfix, class coordtype>
inline int boundarycoef (const tCellFix<dimfix,coordtype> &q, int i)
{
	return CubicalBoundaryCoef (q, i);
} /* boundarycoef */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CELLFIX_H_ 

/// @}

