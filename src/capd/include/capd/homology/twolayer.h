/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file twolayer.h
///
/// This file contains the definition of two-layer cubical sets,
/// as introduced in the paper "Excision-preserving cubical approach
/// to the algorithmic computation of the discrete Conley index"
/// by Kinga Stolot and Pawel Pilarczyk.
/// In addition to the classes that implement the idea of two-layer
/// full cubes and elementary cubes, specializations of some operations
/// used in the homology computation software are also implemented.
/// See the program "homcub2l.cpp" for a sample application
/// of the two-layer cubical sets defined in this header file
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in May 2006. Last revision: May 31, 2010.


#ifndef _CAPD_HOMOLOGY_TWOLAYER_H_ 
#define _CAPD_HOMOLOGY_TWOLAYER_H_ 

#include "capd/homology/cube.h"
#include "capd/homology/cell.h"
#include "capd/homology/neighbor.h"
#include "capd/homology/cubmaps.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/textfile.h"

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstring>
#include <exception>

namespace capd {
namespace homology {


/// The type of the layer variable. It holds the values for the layer
/// numbers (0 and 1), as well as the layer numbers of the Cartesian
/// product of cubes obtained from the layers by bitwise OR on the layer
/// of the first cube shifted by 2 bits to the left and the layer of the
/// other cube.
typedef short int theLayerType;


// --------------------------------------------------
// ---------------- two-layer cubes -----------------
// --------------------------------------------------

template <class tCell>
class tCell2l;

/// A (hyper)cube with additional information about the layer number.
/// By default, the layer number is zero, unless set otherwise.
template <class tCube>
class tCube2l
{
public:
	/// The type for keeping the layer number.
	typedef theLayerType LayerType;

	/// The type for keeping the cube at the given layer.
	typedef tCube CubeType;

	/// The type of the coordinates.
	typedef typename tCube::CoordType CoordType;

	/// The type of a cell related to this cube type.
	typedef tCell2l<typename tCube::CellType> CellType;

	/// The maximal dimension of a cube.
	static const int MaxDim = tCube::MaxDim;

	/// The point base (for wrapping and tabulating coordinates).
	typedef typename tCube::PointBase PointBase;

	/// The default constructor.
	tCube2l ();
	
	/// The constructor of a cube at a given layer.
	tCube2l (const tCube &_q, const LayerType &_l);

	/// The constructor from a table of coordinates.
	tCube2l (const CoordType *coord, int dim);

	/// The constructor from a table of coordinates and a layer.
	tCube2l (const CoordType *coord, int dim, const LayerType &_l);

	/// The constructor from a number (if valid for the base class).
	tCube2l (int_t number, int dim);

	/// The copy constructor.
	tCube2l (const tCube2l &c);

	/// The assignment operator.
	tCube2l &operator = (const tCube2l &c);

	/// Returns the dimension of the cube.
	int dim () const;

	/// Fills out the coordinate table with the cube's coordinates.
	template <class intType>
	intType *coord (intType *c) const;

	/// Returns the hash key no. 1 required by the hashing set template.
	int_t hashkey1 () const;

	/// Returns the hash key no. 2 required by the hashing set template.
	int_t hashkey2 () const;

	/// Returns the name of the objects represented by this class.
	static const char *name ();

	/// Returns the plural name of the objects represented by this class.
	static const char *pluralname ();

	/// Returns the layer number.
	const LayerType &layer () const;

	/// Returns the cube without the layer.
	const tCube &cube () const;

	/// Sets the layer number.
	void layer (const typename tCube2l<tCube>::LayerType &newlayer);

	/// Defines the set of cubes at layer 1 (X).
	/// All the other cubes are at layer 0, and the layers are glued
	/// along the intersection between X and A.
	/// The sets X and A must be disjoint.
	/// A should only contain the neighbors of X.
	static void setlayers (const hashedset<tCube> &X,
		const hashedset<tCube> &A);

	/// Returns the set of cubes at layer 1.
	static const hashedset<tCube> &layer1 ();

	/// Returns the set of cubes at the boundary of layer 1.
	static const hashedset<tCube> &layer1b ();

	/// Returns the set of cubes at layer 0 which are neighbors
	/// of cubes at layer 1 by the identification of layers.
	static const hashedset<tCube> &layer0 ();

private:
	/// The actual cube at the given layer.
	tCube q;

	/// The layer to which the cube belongs.
	LayerType l;

	/// The set of full-dimensional cubes at layer 1.
	/// The identification takes place at the boundary
	/// of these cubes with the set defined as layer 0.
	static hashedset<tCube> layer1set;

	/// The set of full-dimensional cubes at layer 1
	/// adjacent to cubes at layer 0.
	static hashedset<tCube> layer1boundary;

	/// The set of full-dimensional cubes at layer 0
	/// which are adjacent to the cubes at layer 1.
	static hashedset<tCube> layer0set;

}; /* class tCube2l */

// --------------------------------------------------

template <class tCube>
hashedset<tCube> tCube2l<tCube>::layer1set (8192);

template <class tCube>
hashedset<tCube> tCube2l<tCube>::layer1boundary (8192);

template <class tCube>
hashedset<tCube> tCube2l<tCube>::layer0set (8192);

// --------------------------------------------------

template <class tCube>
inline tCube2l<tCube>::tCube2l (): q (), l (0)
{
	return;
} /* tCube2l */

template <class tCube>
inline tCube2l<tCube>::tCube2l (const tCube &_q, const LayerType &_l)
: q (_q), l (_l)
{
	return;
} /* tCube2l */

template <class tCube>
inline tCube2l<tCube>::tCube2l (const CoordType *coord, int dim):
	q (coord, dim), l (layer1set. check (q) ? 1 : 0)
{
	return;
} /* tCube2l */

template <class tCube>
inline tCube2l<tCube>::tCube2l (const CoordType *coord, int dim,
	const LayerType &_l): q (coord, dim), l (_l)
{
	return;
} /* tCube2l */

template <class tCube>
inline tCube2l<tCube>::tCube2l (int_t number, int dim)
: q (number, dim), l (layer1set. check (q) ? 1 : 0)
{
	return;
} /* tCube2l */

template <class tCube>
inline tCube2l<tCube>::tCube2l (const tCube2l &c): q (c. q), l (c. l)
{
	return;
} /* tCube2l */

template <class tCube>
inline tCube2l<tCube> &tCube2l<tCube>::operator = (const tCube2l<tCube> &c)
{
	q = c. q;
	l = c. l;
	return *this;
} /* tCube2l */

template <class tCube>
inline int tCube2l<tCube>::dim () const
{
	return q. dim ();
} /* dim */

template <class tCube>
template <class intType>
inline intType *tCube2l<tCube>::coord (intType *c) const
{
	return q. coord (c);
} /* coord */

template <class tCube>
inline int_t tCube2l<tCube>::hashkey1 () const
{
	return q. hashkey1 ();
} /* hashkey1 */

template <class tCube>
inline int_t tCube2l<tCube>::hashkey2 () const
{
	return q. hashkey2 () ^ l;
} /* hashkey2 */

template <class tCube>
inline const char *tCube2l<tCube>::name ()
{
	return tCube::name ();
} /* name */

template <class tCube>
inline const char *tCube2l<tCube>::pluralname ()
{
	return tCube::pluralname ();
} /* pluralname */

template <class tCube>
inline const tCube &tCube2l<tCube>::cube () const
{
	return q;
} /* cube */

template <class tCube>
inline const typename tCube2l<tCube>::LayerType &tCube2l<tCube>::layer ()
	const
{
	return l;
} /* layer */

template <class tCube>
inline void tCube2l<tCube>::layer
	(const typename tCube2l<tCube>::LayerType &newlayer)
{
	l = newlayer;
	return;
} /* layer */

template <class tCube>
inline void tCube2l<tCube>::setlayers (const hashedset<tCube> &X,
	const hashedset<tCube> &A)
{
	// remember the sets at the layers' boundary
	layer0set = A;
	layer1set = X;
	hashedset<tCube> empty;
	layer1boundary = empty;

	// if the set X is empty, then there is no problem at all
	if (X. empty ())
		return;

	// determine the set at Layer 1 as neighbors of A in X,
	// and create cells at the layers' boundary for identification
	hashedset<typename tCube::CellType> idcells;
	for (int_t i = 0; i < X. size (); ++ i)
	{
		const tCube &q = X [i];
		hashedset<tCube> neighbors;
		int_t ncount = getneighbors (q, 0, layer0set, &neighbors, 0);
		if (!ncount)
			continue;
		layer1boundary. add (q);
		for (int_t j = 0; j < ncount; ++ j)
		{
			idcells. add (typename tCube::CellType
				(q, neighbors [j]));
		}
	}

	// add boundaries of all the cells
	for (int_t i = 0; i < idcells. size (); ++ i)
	{
		const typename tCube::CellType &c = idcells [i];
		int bsize = boundarylength (c);
		for (int j = 0; j < bsize; ++ j)
			idcells. add (boundarycell (c, j));
	}

	// define the identification set
	CellType::identify (idcells, layer1set [0]. dim ());
	return;
} /* setlayers */

template <class tCube>
inline const hashedset<tCube> &tCube2l<tCube>::layer1 ()
{
	return layer1set;
} /* layer1 */

template <class tCube>
inline const hashedset<tCube> &tCube2l<tCube>::layer1b ()
{
	return layer1boundary;
} /* layer1b */

template <class tCube>
inline const hashedset<tCube> &tCube2l<tCube>::layer0 ()
{
	return layer0set;
} /* layer0 */

// --------------------------------------------------

/// The operator == verifies if two cubes are equal.
template <class tCube>
inline int operator == (const tCube2l<tCube> &c1,
	const tCube2l<tCube> &c2)
{
	return (c1. cube () == c2. cube ()) &&
		(c1. layer () == c2. layer ());
} /* operator == */

/// The operator != verifies whether two cubes are different.
/// (Uses the == operator.)
template <class tCube>
inline int operator != (const tCube2l<tCube> &c1,
	const tCube2l<tCube> &c2)
{
	return !(c1 == c2);
} /* operator != */

/// The operator * computes the Cartesian product of two cubes.
template <class tCube>
inline tCube2l<tCube> operator * (const tCube2l<tCube> &c1,
	const tCube2l<tCube> &c2)
{
	tCube q (c1. cube () * c2. cube ());
	typename tCube2l<tCube>::LayerType
		l ((c1. layer () << 2) | c2. layer ());
	return tCube2l<tCube> (q, l);
} /* operator * */

/// The operator << writes a cube to the output stream in the text mode.
template <class tCube>
inline std::ostream &operator << (std::ostream &out, const tCube2l<tCube> &c)
{
	// write the cube
	WriteCube (out, c. cube ());

	// write the layer if any
	if (c. layer ())
		out << '^' << c. layer ();

	return out;
} /* operator << */

/// The operator >> reads a cube from the input stream in the text mode.
template <class tCube>
inline std::istream &operator >> (std::istream &in, tCube2l<tCube> &c)
{
	// read the cube
	tCube q;
	ReadCube (in, q);

	// read the layer if any
	typename tCube2l<tCube>::LayerType l (0);
	ignorecomments (in);
	if (in. peek () == '^')
	{
		in. get ();
		ignorecomments (in);
		in >> l;
	}
	else if (tCube2l<tCube>::layer1 (). check (q))
		l = 1;

	c = tCube2l<tCube> (q, l);
	return in;
} /* operator >> */

/// A specialized version of the operator >> for reading a set of cubes
/// and ignores the first line "dimension N".
template <class tCube>
inline std::istream &operator >> (std::istream &in,
	hashedset<tCube2l<tCube> > &s)
{
	return ReadCubes (in, s);
} /* operator >> */

/// A specialized version of the operator >> that reads a combinatorial
/// cubical multivalued map.
/// This version allows one to use two formats which are automatically
/// distinguished. The assignments can be either like in a generic
/// multivalued map, or in Jacek and Marcin's format (see the chmap program).
template <class tCube>
inline std::istream &operator >> (std::istream &in,
	mvmap<tCube2l<tCube>,tCube2l<tCube> > &m)
{
	return ReadCubicalMap (in, m);
} /* operator >> */


// --------------------------------------------------
// ---------------- two-layer cells -----------------
// --------------------------------------------------

/// A general cubical cell with additional information about the layer
/// number. By default, the layer number is zero, unless set otherwise.
template <class tCell>
class tCell2l
{
public:
	/// The type for keeping the layer number.
	typedef theLayerType LayerType;

	/// The type for keeping the cell at the given layer.
	typedef tCell CellType;

	/// The type of the coordinates.
	typedef typename tCell::CoordType CoordType;
	
	/// The maximal dimension of a cube.
	static const int MaxDim = tCell::MaxDim;

	/// The point base (for wrapping and tabulating coordinates).
	typedef typename tCell::PointBase PointBase;

	/// The default constructor.
	tCell2l ();
	
	/// The constructor of a cell at a given layer.
	tCell2l (const tCell &_q, const LayerType &_l);

	/// The constructor of a cell spanning from one point to another.
	tCell2l (const CoordType *c1, const CoordType *c2,
		int spcdim, int celldim = -1, int layer = 0);

	/// The constructor of a cell as an intersection of two cubes.
	template <class tCube>
	tCell2l (const tCube2l<tCube> &q1, const tCube2l<tCube> &q2);

	/// The constructor of an arbitrary k-dimensional face
	/// of a full cube.
	template <class tCube>
	tCell2l (const tCube2l<tCube> &c, int facedim);

	/// The constructor of a full-dimensional cubical cell.
	template <class tCube>
	explicit tCell2l (const tCube2l<tCube> &c);

	/// The constructor of a projection of a cell
	/// to the given number of coordinates
	/// that start at the given offset.
	template <class tCellSrc>
	tCell2l (const tCell2l<tCellSrc> &q, int offset, int ncoords);

	/// The copy constructor.
	tCell2l (const tCell2l &c);

	/// The assignment operator.
	tCell2l &operator = (const tCell2l &c);

	/// Returns the dimension of the cubical cell.
	int dim () const;

	/// Returns the dimension of the embedding space.
	int spacedim () const;

	/// Fills the given table with the left corner coordinates.
	template <class intType>
	intType *leftcoord (intType *c) const;

	/// Fills the given table with the right corner coordinates.
	template <class intType>
	intType *rightcoord (intType *c) const;

	/// Returns the hash key no. 1 required by the hashing set template.
	int_t hashkey1 () const;

	/// Returns the hash key no. 2 required by the hashing set template.
	int_t hashkey2 () const;

	/// Returns the name of the objects represented by this class.
	static const char *name ();

	/// Returns the plural name of the objects represented by this class.
	static const char *pluralname ();

	/// How to output the cell: As a cartesian product or by two
	/// opposite vertices? Also, should ' ' be inserted?
	enum OutputBitValues
	{
		BitProduct = 0x01,	// unset => two vertices
		BitSpace = 0x02
	};
	static int OutputBits;

	/// Returns the layer number.
	const LayerType &layer () const;

	/// Returns the cell without the layer.
	const tCell &cell () const;

	/// Sets the layer number.
	void layer (const typename tCell2l<tCell>::LayerType &newlayer);

	/// Sets the given set of cells for the identification of layers.
	static void identify (const hashedset<tCell> &s, int dim);

	/// Returns the set of cells for the identification of layers.
	static const hashedset<tCell> &identify ();

	/// Drops the layer of the cell if necessary by the identification.
	static LayerType droplayer (const tCell &q, const LayerType &layer);

private:
	/// The set of cells at which the identification takes place.
	static hashedset<tCell> idset;

	/// The space dimension of cells for which the identification
	/// takes place. For twice this dimension, the cells are
	/// identified by considering both projections.
	static int iddim;

	/// The actual cubical cell at the given layer.
	tCell q;

	/// The layer to which the cell belongs.
	LayerType l;

}; /* class tCell2l */

// --------------------------------------------------

template <class tCell>
int tCell2l<tCell>::OutputBits = 0;

template <class tCell>
hashedset<tCell> tCell2l<tCell>::idset (8192);

template <class tCell>
int tCell2l<tCell>::iddim (0);

// --------------------------------------------------

template <class tCell>
inline tCell2l<tCell>::tCell2l (): q (), l (0)
{
	return;
} /* tCell2l */

template <class tCell>
inline tCell2l<tCell>::tCell2l (const tCell &_q, const LayerType &_l)
: q (_q), l (_l)
{
	if ((l == 1) && idset. check (q))
		l = 0;
	return;
} /* tCell2l */

template <class tCell>
inline tCell2l<tCell>::tCell2l (const typename tCell2l<tCell>::CoordType *c1,
	const typename tCell2l<tCell>::CoordType *c2,
	int spcdim, int celldim, int layer)
: q (c1, c2, spcdim, celldim), l (layer)
{
	if ((l == 1) && idset. check (q))
		l = 0;
	return;
} /* tCell2l */

template <class tCell>
template <class tCube>
inline tCell2l<tCell>::tCell2l (const tCube2l<tCube> &q1,
	const tCube2l<tCube> &q2)
: q (q1. cube (), q2. cube ()), l ((q1. layer () < q2. layer ()) ?
	q1. layer () : q2. layer ())
{
	if ((l == 1) && idset. check (q))
		l = 0;
	return;
} /* tCell2l */

template <class tCell>
template <class tCube>
inline tCell2l<tCell>::tCell2l (const tCube2l<tCube> &c, int facedim)
: q (c. cube (), facedim), l (c. layer ())
{
	l = tCell2l<tCell>::droplayer (q, l);
	return;
} /* tCell2l */

template <class tCell>
template <class tCube>
inline tCell2l<tCell>::tCell2l (const tCube2l<tCube> &c)
: q (c. cube ()), l (c. layer ())
{
	if ((l == 1) && idset. check (q))
		l = 0;
	return;
} /* tCell2l */

template <class tCell>
template <class tCellSrc>
inline tCell2l<tCell>::tCell2l (const tCell2l<tCellSrc> &c,
	int offset, int ncoords)
: q (c. cell (), offset, ncoords), l (c. layer ())
{
	if (offset > 0)
		l &= 0x03;
	else
	{
		l >>= 2;
		l &= 0x03;
	}
	if ((l == 1) && idset. check (q))
		l = 0;
	return;
} /* tCell2l */

template <class tCell>
inline tCell2l<tCell>::tCell2l (const tCell2l &c): q (c. q), l (c. l)
{
	return;
} /* tCell2l */

template <class tCell>
inline tCell2l<tCell> &tCell2l<tCell>::operator = (const tCell2l<tCell> &c)
{
	q = c. q;
	l = c. l;
	return *this;
} /* tCell2l */

template <class tCell>
inline int tCell2l<tCell>::dim () const
{
	return q. dim ();
} /* dim */

template <class tCell>
inline int tCell2l<tCell>::spacedim () const
{
	return q. spacedim ();
} /* spacedim */

template <class tCell>
template <class intType>
inline intType *tCell2l<tCell>::leftcoord (intType *c) const
{
	return q. leftcoord (c);
} /* leftcoord */

template <class tCell>
template <class intType>
inline intType *tCell2l<tCell>::rightcoord (intType *c) const
{
	return q. rightcoord (c);
} /* rightcoord */

template <class tCell>
inline int_t tCell2l<tCell>::hashkey1 () const
{
	return q. hashkey1 ();
} /* hashkey1 */

template <class tCell>
inline int_t tCell2l<tCell>::hashkey2 () const
{
	return q. hashkey2 () ^ l;
} /* hashkey2 */

template <class tCell>
inline const char *tCell2l<tCell>::name ()
{
	return tCell::name ();
} /* name */

template <class tCell>
inline const char *tCell2l<tCell>::pluralname ()
{
	return tCell::pluralname ();
} /* pluralname */

template <class tCell>
inline const typename tCell2l<tCell>::LayerType &tCell2l<tCell>::layer ()
	const
{
	return l;
} /* layer */

template <class tCell>
inline const tCell &tCell2l<tCell>::cell () const
{
	return q;
} /* cell */

template <class tCell>
inline void tCell2l<tCell>::layer
	(const typename tCell2l<tCell>::LayerType &newlayer)
{
	l = newlayer;
	return;
} /* layer */

template <class tCell>
inline void tCell2l<tCell>::identify (const hashedset<tCell> &s, int dim)
{
	idset = s;
	iddim = dim;
	return;
} /* identify */

template <class tCell>
inline const hashedset<tCell> &tCell2l<tCell>::identify ()
{
	return idset;
} /* identify */

template <class tCell>
inline typename tCell2l<tCell>::LayerType tCell2l<tCell>::droplayer
	(const tCell &q, const LayerType &layer)
{
	if (!layer)
		return layer;
	int dim = q. spacedim ();
	if (dim <= iddim)
	{
		if (idset. check (q))
			return 0;
		else
			return layer;
	}
	if (dim != iddim + iddim)
		throw "Unknown cells for layer analysis.";
	typename tCell2l<tCell>::LayerType layer1 (layer >> 2);
	typename tCell2l<tCell>::LayerType layer2 (layer & 0x03);
	if ((layer1) && idset. check (tCell (q, 0, iddim)))
		layer1 = 0;
	if ((layer2) && idset. check (tCell (q, iddim, iddim)))
		layer2 = 0;
	return (layer1 << 2) | layer2;
} /* droplayer */

// --------------------------------------------------

/// The operator == verifies if two cells are equal.
template <class tCell>
inline int operator == (const tCell2l<tCell> &c1,
	const tCell2l<tCell> &c2)
{
	return (c1. cell () == c2. cell ()) &&
		(c1. layer () == c2. layer ());
} /* operator == */

/// The operator != verifies whether two cubes are different.
/// (Uses the == operator.)
template <class tCell>
inline int operator != (const tCell2l<tCell> &c1,
	const tCell2l<tCell> &c2)
{
	return !(c1 == c2);
} /* operator != */

/// The operator * computes the Cartesian product of two cells.
template <class tCell>
inline tCell2l<tCell> operator * (const tCell2l<tCell> &c1,
	const tCell2l<tCell> &c2)
{
	tCell q (c1. cell () * c2. cell ());
	typename tCell2l<tCell>::LayerType
		l ((c1. layer () << 2) | c2. layer ());
	return tCell2l<tCell> (q, l);
} /* operator * */

/// The operator << writes a cubical cell to the text output stream.
template <class tCell>
inline std::ostream &operator << (std::ostream &out, const tCell2l<tCell> &c)
{
	// write the cubical cell
	WriteCubicalCell (out, c. cell ());

	// write the layer if any
	if (c. layer ())
		out << '^' << c. layer ();

	return out;
} /* operator << */

/// The operator >> reads a cubical cell from the text input stream.
template <class tCell>
inline std::istream &operator >> (std::istream &in, tCell2l<tCell> &c)
{
	// read the cubical cell
	tCell q;
	ReadCubicalCell (in, q);

	// read the layer if any
	typename tCell2l<tCell>::LayerType l (0);
	ignorecomments (in);
	if (in. peek () == '^')
	{
		in. get ();
		ignorecomments (in);
		in >> l;
	}

	c = tCell2l<tCell> (q, l);
	return in;
} /* operator >> */

// --------------------------------------------------

/// Computes the given boundary element of a cell. If only existing cells
/// are considered and the requested cell doesn't exist, returns '*this'.
template <class tCell>
inline tCell2l<tCell> boundarycell (const tCell2l<tCell> &q, int i,
	bool onlyexisting)
{
	tCell c = CubicalBoundaryCell (q. cell (), i, onlyexisting);
	if (c == q. cell ())
		return q;
	typename tCell2l<tCell>::LayerType l
		(tCell2l<tCell>::droplayer (c, q. layer ()));
	return tCell2l<tCell> (c, l);
} /* boundarycell */

/// Computes the given boundary element of a cell.
template <class tCell>
inline tCell2l<tCell> boundarycell (const tCell2l<tCell> &q, int i)
{
	tCell c = CubicalBoundaryCell (q. cell (), i);
	typename tCell2l<tCell>::LayerType l
		(tCell2l<tCell>::droplayer (c, q. layer ()));
	return tCell2l<tCell> (c, l);
} /* boundarycell */
	
/// Returns the length of the boundary of a cell.
template <class tCell>
inline int boundarylength (const tCell2l<tCell> &q)
{
	return CubicalBoundaryLength (q. cell ());
} /* boundarylength */

/// Returns the given coefficient in the boundary of a cell.
template <class tCell>
inline int boundarycoef (const tCell2l<tCell> &q, int i)
{
	return CubicalBoundaryCoef (q. cell (), i);
} /* boundarycoef */


// --------------------------------------------------
// ---------------- specializations -----------------
// --------------------------------------------------

/// Specialization of the "bit2neighbor" function for two-layer cubes.
/// Throws an exception, because there might be more than one neighbor
/// in the given direction.
template <class tCube>
inline tCube2l<tCube> bit2neighbor (const tCube2l<tCube> &q, int_t number,
	bool unconditional = false)
{
	throw "Trying to use 'bit2neighbor' for a 2-layer cube.";
	return q;
} /* bit2neighbor */

/// Specialization of the "neighbor2bit" function for two-layer cubes.
/// Throws an exception, because there might be more than one bit
/// which cescribes the intersection.
template <class tCube>
int_t neighbor2bit (const tCube2l<tCube> &q, const tCube2l<tCube> &neighbor)
{
	throw "Trying to use 'neighbor2bit' for a 2-layer cube.";
	return -1;
} /* neighbor2bit */

/// Computes the intersection between two cubes at different layers.
/// One cube is at layer 1, and the other is at layer 0, but not in the
/// set on which the identification takes place.
/// The intersection directions are marked in the given bit field.
/// Returns true iff the intersection is nonempty.
template <class tCube>
bool intersection2l (const tCube &q0, const tCube &q1, BitField *bits)
{
	// determine the set of cells at the intersection of layers
	const hashedset<typename tCube::CellType> &ident =
		tCell2l<typename tCube::CellType>::identify ();

	// compute the intersection of the cubes
	typename tCube::CellType intersection (q0, q1);
	hashedset<typename tCube::CellType> faces;
	faces. add (intersection);

	// check all the faces of the cells
	int_t current = 0;
	int_t counter = 0;
	while (current < faces. size ())
	{
		const typename tCube::CellType &face = faces [current ++];
		if (ident. check (face))
		{
			if (bits)
				bits -> set (neighbor2bit (q0, face));
			++ counter;
		}
		else
		{
			for (int_t i = 0; i < boundarylength (face); ++ i)
				faces. add (boundarycell (face, i));
		}
	}
	return (counter > 0);
} /* intersection2l */

/// Specialization of the function which gets neighbors of the given cube
/// by scanning the entire set of possible neighbors.
template <class tCube, class tCubeSet1, class tCubeSet2>
int_t getneighbors_scan (const tCube2l<tCube> &q2l, BitField *bits,
	const tCubeSet1 &theset, tCubeSet2 *neighbors, int_t limit)
{
	// decompose the cube into its components
	const tCube &q0 = q2l. cube ();
	typename tCube2l<tCube>::LayerType l0 (q2l. layer ());

	// determine the set of cubes at layer 0
	const hashedset<tCube> &layer0 = tCube2l<tCube>::layer0 ();

	// prepare a counter for the number of neighbors
	int_t count = 0;

	// go through all the elements in the set
	for (int_t i = 0; i < theset. size (); ++ i)
	{
		// take the cube from the set
		const tCube2l<tCube> &q1l = theset [i];

		// if this is the current cube then ignore it
		if (q1l == q2l)
			continue;

		// decompose the cube into its components
		const tCube &q1 = q1l. cube ();
		typename tCube2l<tCube>::LayerType l1 (q1l. layer ());

		// determine the number of this neighbor
		int_t number = neighbor2bit (q0, q1);

		// if not neighbor then ignore it
		if (number < 0)
			continue;

		// if the cubes fully intersect then this is easy
		if ((l0 == l1) ||
			((l0 == 0) && (l1 == 1) && (layer0. check (q0))) ||
			((l0 == 1) && (l1 == 0) && (layer0. check (q1))))
		{
			// set the appropriate bit in the bit field
			if (bits)
				bits -> set (number);
		}
		// otherwise the correct intersection of the cubes
		// must be determined at the boundary between the layers
		else if (!intersection2l (q0, q1, bits))
			continue;

		// add the cube to the set of neighbors
		if (neighbors)
			neighbors -> add (q1l);

		// increase the counter
		++ count;

		// if this is enough then finish
		if (limit && (count >= limit))
			return count;
	}

	return count;
} /* getneighbors_scan */

/// Specialization of the function which gets neighbors of the given cube
/// by generating all the possible neighbors and checking if they are
/// present in the given set.
template <class tCube, class tCubeSet1, class tCubeSet2>
int_t getneighbors_generate (const tCube2l<tCube> &q2l, BitField *bits,
	const tCubeSet1 &theset, tCubeSet2 *neighbors, int_t limit)
{
	// decompose the cube into its components
	const tCube &q0 = q2l. cube ();
	typename tCube2l<tCube>::LayerType l0 (q2l. layer ());

	// determine the upper bound for the number of neighbors
	int_t maxneighbors = getmaxneighbors (q0. dim ());

	// determine the set of cubes at layer 0
	const hashedset<tCube> &layer0 = tCube2l<tCube>::layer0 ();

	// determine the set of cubes at layer 1
	const hashedset<tCube> &layer1 = tCube2l<tCube>::layer1 ();

	// prepare a counter for the number of neighbors
	int_t count = 0;

	// go through all possible neighbor numbers
	for (int_t number = 0; number < maxneighbors; ++ number)
	{
		// create a neighbor cube using the generic algorithm
		tCube q1 = bit2neighbor (q0, number, true);

		// determine the layer of the neighbor
		int l1 = layer1. check (q1) ? 1 : 0;

		// create the neighbor cube
		tCube2l<tCube> q1l (q1, l1);

		// if this cube is not in the set then skip it
		if (!theset. check (q1l))
			continue;

		// if the cubes fully intersect then this is easy
		if ((l0 == l1) ||
			((l0 == 0) && (l1 == 1) && (layer0. check (q0))) ||
			((l0 == 1) && (l1 == 0) && (layer0. check (q1))))
		{
			// set the appropriate bit in the bit field
			if (bits)
				bits -> set (number);
		}
		// otherwise the correct intersection of the cubes
		// must be determined at the boundary between the layers
		else if (!intersection2l (q0, q1, bits))
			continue;

		// add the cube to the set of neighbors
		if (neighbors)
			neighbors -> add (q1l);

		// increase the counter
		++ count;

		// if this is enough then finish
		if (limit && (count >= limit))
			return count;
	}

	return count;
} /* getneighbors_generate */

/// Specialization of the "createimages" function for two-layer cubes.
/// This function creates images of cells in 'm' as unions of cubes
/// determined by f1 and f2.
/// The domains of interest are given explicitly.
/// Returns the total number of cubes in all the images of cells.
template <class euclidom, class tCell, class tCube>
int_t createimages (mvcellmap<tCell2l<tCell>,euclidom,tCube2l<tCube> > &m,
	const mvmap<tCube2l<tCube>,tCube2l<tCube> > &f1,
	const mvmap<tCube2l<tCube>,tCube2l<tCube> > &f2,
	const hashedset<tCube2l<tCube> > &dom1,
	const hashedset<tCube2l<tCube> > &dom2)
{
	typedef typename tCube::CoordType coordType;
	int_t countimages = 0;
	coordType leftbound [tCell::MaxDim];
	coordType rightbound [tCell::MaxDim];
	coordType left [tCell::MaxDim];
	coordType right [tCell::MaxDim];

	// go through all the dimensions of the cellular complex separtely
	for (int d = 0; d <= m. dim (); ++ d)
	{
		const hashedset<tCell2l<tCell> > &cset = m. get (d);
		if (cset. empty ())
			continue;
		const int spacedim = cset [0]. spacedim ();

		// go through the cells of the specified dimension
		for (int_t i = 0; i < cset. size (); ++ i)
		{
			// remember the cell whose image is computed
			const tCell2l<tCell> &thecell = cset [i];

			// determine tha layer of the cell
			const typename tCube2l<tCube>::LayerType layer =
				thecell. layer ();

			// check if the layers are identified at the cell
			bool idlayers = tCell2l<tCell>::identify ().
				check (thecell. cell ());

			// get the coordinates of the corners of the cell
			thecell. leftcoord (left);
			thecell. rightcoord (right);

			// compute the bounds for full cubes to get imgs of
			for (int j = 0; j < spacedim; ++ j)
			{
				// compensate for space wrapping
				if (right [j] < left [j])
					right [j] = left [j] + 1;

				// compute the bounds for full cubes
				leftbound [j] = static_cast<coordType>
					(left [j] - (left [j] == right [j]));
				rightbound [j] = static_cast<coordType>
					(right [j] +
					(left [j] == right [j]));
			}

			// go through the full cubes in the computed range
			tRectangle<coordType> r (leftbound, rightbound,
				spacedim);
			const coordType *c;
			while ((c = r. get ()) != NULL)
			{
				// determine the core cube
				if (!tCube::PointBase::check (c, spacedim))
					continue;
				tCube q0 (c, spacedim);

				// add the images of the 2-layer cube
				tCube2l<tCube> q (q0, layer);
				if (dom1. check (q))
					m. add (d, i, f1 (q));
				if (dom2. check (q))
					m. add (d, i, f2 (q));

				// determine if the cubes at the other
				// layer must also be considered
				typename tCube2l<tCube>::LayerType l = layer;
				if (idlayers && !layer &&
					tCube2l<tCube>::layer1 ().
					check (q0))
				{
					l = 1;
				}
				else if (idlayers && layer &&
					tCube2l<tCube>::layer0 ().
					check (q0))
				{
					l = 0;
				}
				if (l != layer)
				{
					tCube2l<tCube> ql (q0, l);
					if (dom1. check (ql))
						m. add (d, i, f1 (ql));
					if (dom2. check (ql))
						m. add (d, i, f2 (ql));
				}
			}
			countimages += m (thecell). size ();
		}
	}
	return countimages;
} /* createimages */


// --------------------------------------------------
// ----------------- standard types -----------------
// --------------------------------------------------

/// A typical full cube in the two-layer setting.
typedef tCube2l<tCubeBase<coordinate> > Cube2l;

/// A typical cubical cell in the two-layer setting.
typedef tCell2l<tCellBase<coordinate> > CubicalCell2l;

/// A typical multivalued map on full cubes in the two-layer setting.
typedef mvmap<Cube2l,Cube2l> CombinatorialMultivaluedMap2l;

/// A typical set of full cubes in the two-layer setting.
typedef hashedset<Cube2l> SetOfCubes2l;

/// A typical set of cubical cells in the two-layer setting.
typedef hashedset<CubicalCell2l> SetOfCubicalCells2l;

/// A typical cubical complex in the two-layer setting.
typedef gcomplex<CubicalCell2l,integer> CubicalComplex2l;

/// A typical multivalued cubical-cellular map in the two-layer setting.
typedef mvcellmap<CubicalCell2l,integer,CubicalCell2l>
	CubicalMultivaluedMap2l;


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_TWOLAYER_H_ 

/// @}

