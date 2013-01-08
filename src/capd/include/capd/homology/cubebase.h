/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubebase.h
///
/// This file contains the definition of full cubes which use
/// a cube base class for indexing all the possible coordinate
/// combinations. This saves a lot of memory if the same points
/// are reused, e.g., if the same cubes appear in different sets.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: May 25, 2010.


#ifndef _CAPD_HOMOLOGY_CUBEBASE_H_ 
#define _CAPD_HOMOLOGY_CUBEBASE_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cubemain.h"

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstring>

namespace capd {
namespace homology {


// a friend class template
template <class coordtype>
class tCellBase;


// --------------------------------------------------
// -------------- Cube with PointBase ---------------
// --------------------------------------------------

/// This class defines a hypercube in R^n with edges parallel to the axes
/// and with size 1 in each direction.
/// This implementation uses a cube base class for indexing
/// all the possible coordinate combinations that appear in the program.
template <class coordtype>
class tCubeBase
{
public:
	/// The type of coordinates of a cube.
	typedef coordtype CoordType;

	/// The type of a cell related to this cube type.
	typedef tCellBase<coordtype> CellType;

	/// The maximal dimension of a cube.
	static const int MaxDim = MaxBasDim;

	/// The point base (for wrapping and tabulating coordinates).
	typedef tPointBase<coordtype> PointBase;

	/// The default constructor.
	tCubeBase ();
	
	/// The constructor of a cube from a table of coordinates.
	tCubeBase (const coordtype *c, int dim);

	/// The constructor of a cube from a number (should be used
	/// with caution).
	tCubeBase (int_t number, int dim);

	/// The copy constructor.
	tCubeBase (const tCubeBase<coordtype> &c);

	/// The assignment operator.
	tCubeBase<coordtype> &operator =
		(const tCubeBase<coordtype> &c);

	/// Returns the dimension of the cube.
	int dim () const;

	/// Fills out the coordinate table with the cube's coordinates.
//	template <class intType>
//	intType *coord (intType *c) const;
	coordtype *coord (coordtype *c) const;

	/// Returns hashing key no. 1 required by the hashing set template.
	int_t hashkey1 () const;

	/// Returns hashing key no. 2 required by the hashing set template.
	int_t hashkey2 () const;

	/// Returns the name of the objects represented by this class.
	static const char *name ();

	/// Returns the plural name of the objects represented by this class.
	static const char *pluralname ();

	// --- friends: ---

	/// The operator == for cubes.
	friend inline int operator == (const tCubeBase<coordtype> &c1,
		const tCubeBase<coordtype> &c2)
	{
		return c1. n == c2. n;
	} /* operator == */

	// friend class: cubical cell
	friend class tCellBase<coordtype>;

private:
	/// Returns the actual number of the cube in the point base.
	int_t num () const;

	/// The number that represents the full cube.
	/// High bits keep the space dimension, the remaining bits
	/// form the number of the cube in an appropriate pointset.
	int_t n;

}; /* class tCubeBase */

// --------------------------------------------------

template <class coordtype>
inline int_t tCubeBase<coordtype>::num () const
{
	return (n & NumMask);
} /* tCubeBase::num */

// --------------------------------------------------

template <class coordtype>
inline tCubeBase<coordtype>::tCubeBase ()
: n (0)
{
	return;
} /* tCubeBase::tCubeBase */

template <class coordtype>
inline tCubeBase<coordtype>::tCubeBase (const coordtype *c,
	int dim)
{
	if (dim <= 0)
		throw "Non-positive dimension of a cube.";
	if (dim >= MaxDim)
		throw "Too high space dimension.";
	n = PointBase::number (c, dim);
	if (n < 0)
		throw "Negative number of a cube.";
	n |= (static_cast<int_t> (dim) << NumBits);
	return;
} /* tCubeBase::tCubeBase */

template <class coordtype>
inline tCubeBase<coordtype>::tCubeBase (int_t number, int dim)
{
	n = number | (static_cast<int_t> (dim) << NumBits);
	return;
} /* tCubeBase::tCubeBase */

template <class coordtype>
inline tCubeBase<coordtype>::tCubeBase (const tCubeBase<coordtype> &c)
{
	n = c. n;
	return;
} /* tCubeBase::tCubeBase */

template <class coordtype>
inline tCubeBase<coordtype> &tCubeBase<coordtype>::operator =
	(const tCubeBase<coordtype> &c)
{
	n = c. n;
	return *this;
} /* tCubeBase::operator = */

template <class coordtype>
inline int tCubeBase<coordtype>::dim () const
{
	return static_cast<int> (n >> NumBits);
} /* tCubeBase::dim */

//template <class coordtype>
//template <class intType>
//inline intType *tCubeBase<coordtype>::coord (intType *c) const
//{
//	int d = dim ();
//	const coordtype *tab = PointBase::coord (num (), d);
//	for (int i = 0; i < d; ++ i)
//		c [i] = static_cast<const intType> (tab [i]);
//	return c;
//} /* tCubeBase::coord */

template <class coordtype>
inline coordtype *tCubeBase<coordtype>::coord (coordtype *c) const
{
	int d = dim ();
	const coordtype *tab = PointBase::coord (num (), d);
	for (int i = 0; i < d; ++ i)
		c [i] = tab [i];
	return c;
} /* tCubeBase::coord */

template <class coordtype>
inline int_t tCubeBase<coordtype>::hashkey1 () const
{
	return static_cast<int_t>
		(((n ^ 0x55555555u) << 17) ^ ((n ^ 0xAA00AA00u) << 7) ^
		((n ^ 0x00AA00AAu) >> 7));
} /* tCubeBase::hashkey1 */

template <class coordtype>
inline int_t tCubeBase<coordtype>::hashkey2 () const
{
	return static_cast<int_t>
		(((n ^ 0xAAAAAAAAu) << 18) ^ ((n ^ 0x55005500u) >> 8) ^
		((n ^ 0x00550055u) << 10));
} /* tCubeBase::hashkey2 */

template <class coordtype>
inline const char *tCubeBase<coordtype>::name ()
{
	return "cube";
} /* tCubeBase::name */

template <class coordtype>
inline const char *tCubeBase<coordtype>::pluralname ()
{
	return "cubes";
} /* tCubeBase::pluralname */

// --------------------------------------------------

/// The operator != for comparing full cubes.
template <class coordtype>
inline int operator != (const tCubeBase<coordtype> &c1,
	const tCubeBase<coordtype> &c2)
{
	return !(c1 == c2);
} /* operator != */

// --------------------------------------------------

/// Computes the Cartesian product of two cubes.
template <class coordtype>
inline tCubeBase<coordtype> operator * (const tCubeBase<coordtype> &c1,
	const tCubeBase<coordtype> &c2)
{
	int dim1 = c1. dim (), dim2 = c2. dim ();
	if (dim1 + dim2 >= tCubeBase<coordtype>::MaxDim)
		throw "Dimension too high to concatenate coordinates.";
	coordtype coord [tCubeBase<coordtype>::MaxDim];
	c1. coord (coord);
	c2. coord (coord + dim1);
	return tCubeBase<coordtype> (coord, dim1 + dim2);
} /* operator * */

// --------------------------------------------------

/// Writes a cube to an output stream in the text mode.
/// The cube is represented by an n-tuple of integers
/// which are the coordinates of the vertex with minimal coordinates.
template <class coordtype>
inline std::ostream &operator << (std::ostream &out,
	const tCubeBase<coordtype> &c)
{
	return WriteCube (out, c);
} /* operator << */

/// Reads a cube from an input stream in the text mode.
/// The cube is represented by an n-tuple of integers
/// which are the coordinates of the vertex with minimal coordinates.
template <class coordtype>
inline std::istream &operator >> (std::istream &in, tCubeBase<coordtype> &c)
{
	return ReadCube (in, c);
} /* operator >> */

/// Reads a set of cubes from an input stream in the text mode.
template <class coordtype>
inline std::istream &operator >> (std::istream &in,
	hashedset<tCubeBase<coordtype> > &s)
{
	return ReadCubes (in, s);
} /* operator >> */

/// Reads a cubical map from an input stream in the text mode.
template <class coordtype>
inline std::istream &operator >> (std::istream &in,
	mvmap<tCubeBase<coordtype>,tCubeBase<coordtype> > &m)
{
	return ReadCubicalMap (in, m);
} /* operator >> */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CUBEBASE_H_ 

/// @}

