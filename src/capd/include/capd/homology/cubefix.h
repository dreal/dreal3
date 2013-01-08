/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubefix.h
///
/// This class defines full cubes in which the embedding space dimension
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

// Started in January 2002. Last revision: June 1, 2007.


#ifndef _CAPD_HOMOLOGY_CUBEFIX_H_ 
#define _CAPD_HOMOLOGY_CUBEFIX_H_ 

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
template <int dimfix, class coordtype>
class tCellFix;


// --------------------------------------------------
// ------------ Cube of fixed dimension -------------
// --------------------------------------------------

/// This class defines a hypercube in R^n with edges parallel to the axes
/// and with size 1 in each direction.
/// This implementation assumes that the embedding space dimension is known
/// at time of compilation.
template <int dimfix, class coordtype>
class tCubeFix
{
public:
	/// The type of coordinates of a cube.
	typedef coordtype CoordType;

	/// The type of a cell related to this cube type.
	typedef tCellFix<dimfix,coordtype> CellType;

	/// The maximal dimension of a cube (unused).
	static const int MaxDim = 512;

	/// The point base (for wrapping and tabulating coordinates).
	typedef tWrapBase<coordtype> PointBase;

	/// The default constructor.
	tCubeFix ();
	
	/// The constructor of a cube from a table of coordinates.
	tCubeFix (const coordtype *c, int dim = 0);

	/// The constructor of a cube from a number (invalid in this class).
	tCubeFix (int number, int dim);

	/// The copy constructor.
	tCubeFix (const tCubeFix<dimfix,coordtype> &c);

	/// The assignment operator.
	tCubeFix<dimfix,coordtype> &operator =
		(const tCubeFix<dimfix,coordtype> &c);

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

	/// The operator == for cubes.
	friend int operator == (const tCubeFix<dimfix,coordtype> &c1,
		const tCubeFix<dimfix,coordtype> &c2)
	{
		return thesame (c1. tab, c2. tab, dimfix);
	}

	// friend class: cubical cell
	friend class tCellFix<dimfix, coordtype>;

private:
	/// A table with the coordinates of the minimal vertex of the cube.
	coordtype tab [dimfix];

}; /* class tCubeFix */

// --------------------------------------------------

template <int dimfix, class coordtype>
inline tCubeFix<dimfix,coordtype>::tCubeFix ()
{
	return;
} /* tCubeFix::tCubeFix */

template <int dimfix, class coordtype>
inline tCubeFix<dimfix,coordtype>::tCubeFix
	(const coordtype *c, int dim)
{
	if (dim && ((dim != dimfix) || (dim < 0)))
		throw "Wrong dimension of a fixed-dim cube.";
	PointBase::wrapcopy (tab, c, dimfix);
	return;
} /* tCubeFix::tCubeFix */

template <int dimfix, class coordtype>
inline tCubeFix<dimfix,coordtype>::tCubeFix (int, int)
{
	throw "Unable to construct a cube from a number.";
} /* tCubeFix::tCubeFix */

template <int dimfix, class coordtype>
inline tCubeFix<dimfix,coordtype>::tCubeFix
	(const tCubeFix<dimfix,coordtype> &c)
{
	for (int i = 0; i < dimfix; ++ i)
		tab [i] = c. tab [i];
	return;
} /* tCubeFix::tCubeFix */

template <int dimfix, class coordtype>
inline tCubeFix<dimfix,coordtype> &tCubeFix<dimfix,coordtype>::operator =
	(const tCubeFix<dimfix,coordtype> &c)
{
	for (int i = 0; i < dimfix; ++ i)
		tab [i] = c. tab [i];
	return *this;
} /* tCubeFix::operator = */

template <int dimfix, class coordtype>
inline int tCubeFix<dimfix,coordtype>::dim () const
{
	return dimfix;
} /* tCubeFix::dim */

//template <int dimfix, class coordtype>
//template <class intType>
//inline intType *tCubeFix<dimfix,coordtype>::coord (intType *c) const
//{
//	for (int i = 0; i < dimfix; ++ i)
//		c [i] = static_cast<const intType> (tab [i]);
//	return c;
//} /* tCubeFix::coord */

template <int dimfix, class coordtype>
inline coordtype *tCubeFix<dimfix,coordtype>::coord (coordtype *c) const
{
	for (int i = 0; i < dimfix; ++ i)
		c [i] = tab [i];
	return c;
} /* tCubeFix::coord */

template <int dimfix, class coordtype>
inline int_t tCubeFix<dimfix,coordtype>::hashkey1 () const
{
	switch (dimfix)
	{
	case 1:
		return static_cast<int_t> (tab [0]) << 12;
	case 2:
		return ((static_cast<int_t> (tab [0])) << 18) +
			((static_cast<int_t> (tab [1])) << 6);
	default:
		return ((static_cast<int_t> (tab [0])) << 18) +
			((static_cast<int_t> (tab [1])) << 6) +
			((static_cast<int_t> (tab [2])) >> 6);
	}
} /* tCubeFix::hashkey1 */

template <int dimfix, class coordtype>
inline int_t tCubeFix<dimfix,coordtype>::hashkey2 () const
{
	switch (dimfix)
	{
	case 1:
		return static_cast<int_t> (tab [0]) << 3;
	case 2:
		return (static_cast<int_t> (tab [0]) >> 1) +
			(static_cast<int_t> (tab [1]) << 13);
	default:
		return ((static_cast<int_t> (tab [dimfix - 1])) << 20) +
			((static_cast<int_t> (tab [dimfix - 2])) << 9) +
			((static_cast<int_t> (tab [dimfix - 3])) >> 1);
	}
} /* tCubeFix::hashkey2 */

template <int dimfix, class coordtype>
const char *tCubeFix<dimfix,coordtype>::name ()
{
	return "cube";
} /* tCubeFix::name */

template <int dimfix, class coordtype>
const char *tCubeFix<dimfix,coordtype>::pluralname ()
{
	return "cubes";
} /* tCubeFix::pluralname */

/// The operator != for comparing full cubes.
template <int dim1, int dim2, class coordtype>
inline int operator != (const tCubeFix<dim1,coordtype> &c1,
	const tCubeFix<dim2,coordtype> &c2)
{
	return !(c1 == c2);
} /* operator != */

// --------------------------------------------------

/// Computes the Cartesian product of two cubes.
template <int dim1, int dim2, class coordtype>
inline tCubeFix<dim1+dim2,coordtype> operator *
	(const tCubeFix<dim1,coordtype> &c1,
	const tCubeFix<dim2,coordtype> &c2)
{
	coordtype coord [dim1 + dim2];
	c1. coord (coord);
	c2. coord (coord + dim1);
	return tCubeFix<dim1+dim2,coordtype> (coord);
} /* operator * */

// --------------------------------------------------

/// Writes a cube to an output stream in the text mode.
/// The cube is represented by an n-tuple of integers
/// which are the coordinates of the vertex with minimal coordinates.
template <int dimfix, class coordtype>
inline std::ostream &operator << (std::ostream &out,
	const tCubeFix<dimfix,coordtype> &c)
{
	return WriteCube (out, c);
} /* operator << */

/// Reads a cube from an input stream in the text mode.
/// The cube is represented by an n-tuple of integers
/// which are the coordinates of the vertex with minimal coordinates.
template <int dimfix, class coordtype>
inline std::istream &operator >> (std::istream &in,
	tCubeFix<dimfix,coordtype> &c)
{
	return ReadCubeFix (in, c, dimfix);
} /* operator >> */

/// Reads a set of cubes from an input stream in the text mode.
template <int dimfix, class coordtype>
inline std::istream &operator >> (std::istream &in,
	hashedset<tCubeFix<dimfix,coordtype> > &s)
{
	return ReadCubes (in, s);
} /* operator >> */

/// Reads a cubical map from an input stream in the text mode.
template <int dimfix, class coordtype>
inline std::istream &operator >> (std::istream &in,
	mvmap<tCubeFix<dimfix,coordtype>,tCubeFix<dimfix,coordtype> > &m)
{
	return ReadCubicalMap (in, m);
} /* operator >> */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CUBEFIX_H_ 

/// @}

