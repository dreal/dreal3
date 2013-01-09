/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubevar.h
///
/// This file defines full cubes whose embedding space dimension
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

// Started in January 2002. Last revision: June 1, 2007.


#ifndef _CAPD_HOMOLOGY_CUBEVAR_H_ 
#define _CAPD_HOMOLOGY_CUBEVAR_H_ 

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
class tCellVar;


// --------------------------------------------------
// ----------- Cube with allocated memory -----------
// --------------------------------------------------

/// This class defines a hypercube in R^n with edges parallel to the axes
/// and with size 1 in each direction.
/// In this implementation, an array is allocated for the coordinates
/// of the minimal vertex of a cube.
template <class coordtype>
class tCubeVar
{
public:
	/// The type of coordinates of a cube.
	typedef coordtype CoordType;

	/// The type of a cell related to this cube type.
	typedef tCellVar<coordtype> CellType;

	/// The maximal dimension of a cube.
	static const int MaxDim = 50;

	/// The point base (for wrapping and tabulating coordinates).
	typedef tWrapBase<coordtype> PointBase;

	/// The default constructor.
	tCubeVar ();
	
	/// The constructor from a table of coordinates.
	tCubeVar (const coordtype *c, int dim);

	/// The constructor from a number (invalid in this class).
	tCubeVar (int number, int dim);

	/// The copy constructor.
	tCubeVar (const tCubeVar<coordtype> &c);

	/// The assignment operator.
	tCubeVar<coordtype> &operator = (const tCubeVar<coordtype> &c);

	/// The destructor.
	~tCubeVar ();

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
	friend inline int operator == (const tCubeVar<coordtype> &c1,
		const tCubeVar<coordtype> &c2)
	{
		if (!c1. tab)
			return c2. tab ? false : true;
		if (!c2. tab)
			return false;
		return thesame (c1. tab, c2. tab, c1. tab [0] + 1);
	} /* operator == */

	// friend class: cubical cell
	friend class tCellVar<coordtype>;

private:
	/// The table containing the coordinates of the cube,
	/// as well as its dimension (at tab [0]).
	coordtype *tab;

	/// Initializes the data for a cube of a given dimension > 0.
	/// Returns the pointer to the coordinates table (i.e. tab + 1).
	coordtype *initialize (int dim);

}; /* class tCubeVar */

// --------------------------------------------------

template <class coordtype>
inline coordtype *tCubeVar<coordtype>::initialize (int d)
{
	tab = new coordtype [d + 1];
	if (!tab)
		throw "Not enough memory for a cube.";
	*tab = d;
	return (tab + 1);
} /* tCubeVar::initialize */

// --------------------------------------------------

template <class coordtype>
inline tCubeVar<coordtype>::tCubeVar ()
{
	tab = NULL;
	return;
} /* tCubeVar::tCubeVar */

template <class coordtype>
inline tCubeVar<coordtype>::tCubeVar (const coordtype *c, int d)
{
	if (d < 0)
		throw "Negative dimension of a cube.";
	if (d)
		PointBase::wrapcopy (initialize (d), c, d);
	else
		tab = NULL;
	return;
} /* tCubeVar::tCubeVar */

template <class coordtype>
inline tCubeVar<coordtype>::tCubeVar (int, int)
{
	throw "Unable to construct a cube from a number.";
} /* tCubeVar::tCubeVar */

template <class coordtype>
inline tCubeVar<coordtype>::tCubeVar (const tCubeVar<coordtype> &c)
{
	if (!c. dim ())
		tab = NULL;
	else
	{
		initialize (c. dim ());
		copycoord (tab + 1, c. tab + 1, c. dim ());
	}
	return;
} /* tCubeVar::tCubeVar */

template <class coordtype>
inline tCubeVar<coordtype> &tCubeVar<coordtype>::operator =
	(const tCubeVar<coordtype> &c)
{
	if (dim () == c. dim ())
		copycoord (tab + 1, c. tab + 1, dim ());
	else
	{
		if (tab)
			delete [] tab;
		if (c. dim ())
		{
			initialize (c. dim ());
			copycoord (tab + 1, c. tab + 1, c. dim ());
		}
		else
			tab = NULL;
	}
	return *this;
} /* tCubeVar::operator = */

template <class coordtype>
inline tCubeVar<coordtype>::~tCubeVar<coordtype> ()
{
	if (tab)
		delete [] tab;
	return;
} /* tCubeVar::~tCubeVar */

template <class coordtype>
inline int tCubeVar<coordtype>::dim () const
{
	return tab ? *tab : 0;
} /* tCubeVar::dim */

//template <class coordtype>
//template <class intType>
//inline intType *tCubeVar<coordtype>::coord (intType *c) const
//{
//	if (!tab)
//		return NULL;
//	for (int i = 0; i < *tab; ++ i)
//		c [i] = static_cast<const intType> (tab [i + 1]);
//	return c;
//} /* tCubeVar::coord */

template <class coordtype>
inline coordtype *tCubeVar<coordtype>::coord (coordtype *c) const
{
	if (!tab)
		return 0;
	for (int i = 0; i < *tab; ++ i)
		c [i] = tab [i + 1];
	return c;
} /* tCubeVar::coord */

template <class coordtype>
inline int_t tCubeVar<coordtype>::hashkey1 () const
{
	int d = dim ();
	switch (d)
	{
	case 0:
		return 0;
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
} /* tCubeVar::hashkey1 */

template <class coordtype>
inline int_t tCubeVar<coordtype>::hashkey2 () const
{
	int d = dim ();
	switch (d)
	{
	case 0:
		return 1;
	case 1:
		return static_cast<int_t> (tab [0]) << 3;
	case 2:
		return (static_cast<int_t> (tab [0]) >> 1) +
			(static_cast<int_t> (tab [1]) << 13);
	default:
		return ((static_cast<int_t> (tab [d - 1])) << 20) +
			((static_cast<int_t> (tab [d - 2])) << 9) +
			((static_cast<int_t> (tab [d - 3])) >> 1);
	}
} /* tCubeVar::hashkey2 */

template <class coordtype>
inline const char *tCubeVar<coordtype>::name ()
{
	return "cube";
} /* tCubeVar::name */

template <class coordtype>
inline const char *tCubeVar<coordtype>::pluralname ()
{
	return "cubes";
} /* tCubeVar::pluralname */

// --------------------------------------------------

/// The operator != for comparing full cubes.
template <class coordtype>
inline int operator != (const tCubeVar<coordtype> &c1,
	const tCubeVar<coordtype> &c2)
{
	return !(c1 == c2);
} /* operator != */

// --------------------------------------------------

/// Computes the Cartesian product of two cubes.
template <class coordtype>
inline tCubeVar<coordtype> operator * (const tCubeVar<coordtype> &c1,
	const tCubeVar<coordtype> &c2)
{
	int dim1 = c1. dim (), dim2 = c2. dim ();
	if (dim1 + dim2 >= tCubeVar<coordtype>::MaxDim)
		throw "Dimension too high to concatenate coordinates.";
	coordtype coord [tCubeVar<coordtype>::MaxDim];
	c1. coord (coord);
	c2. coord (coord + dim1);
	return tCubeVar<coordtype> (coord, dim1 + dim2);
} /* operator * */

// --------------------------------------------------

/// Writes a cube to an output stream in the text mode.
/// The cube is represented by an n-tuple of integers
/// which are the coordinates of the vertex with minimal coordinates.
template <class coordtype>
inline std::ostream &operator << (std::ostream &out,
	const tCubeVar<coordtype> &c)
{
	return WriteCube (out, c);
} /* operator << */

/// Reads a cube from an input stream in the text mode.
/// The cube is represented by an n-tuple of integers
/// which are the coordinates of the vertex with minimal coordinates.
template <class coordtype>
inline std::istream &operator >> (std::istream &in, tCubeVar<coordtype> &c)
{
	return ReadCube (in, c);
} /* operator >> */

/// Reads a set of cubes from an input stream in the text mode.
template <class coordtype>
inline std::istream &operator >> (std::istream &in,
	hashedset<tCubeVar<coordtype> > &s)
{
	return ReadCubes (in, s);
} /* operator >> */

/// Reads a cubical map from an input stream in the text mode.
template <class coordtype>
inline std::istream &operator >> (std::istream &in,
	mvmap<tCubeVar<coordtype>,tCubeVar<coordtype> > &m)
{
	return ReadCubicalMap (in, m);
} /* operator >> */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CUBEVAR_H_ 

/// @}

