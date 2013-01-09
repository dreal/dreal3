/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cellmain.h
///
/// This file contains the definition of some functions that are common
/// for all types of cubical cells, independent of the details of their
/// implementation, mainly the computation of the boundary of a cell
/// and text input/output procedures.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: July 15, 2007.


#ifndef _CAPD_HOMOLOGY_CELLMAIN_H_ 
#define _CAPD_HOMOLOGY_CELLMAIN_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/chains.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/gcomplex.h"
#include "capd/homology/pointbas.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------- CUBICAL CELL BOUNDARY --------------
// --------------------------------------------------

/// Returns the i-th boundary element of a cell.
/// If only existing cells are considered,
/// returns '*this' if the requested boundary cell doesn't exist.
///
/// For a cubical cell whose non-zero intervals in the Cartesian product
/// are [p1-,p1+], [p2-,p2+], etc., the boundary
/// is an alternating sum of cells
/// in which these intervals are replaced by single elements,
/// first by those with larger values (signs begin with a '+'),
/// and then by those with smaller values (signs begin with a '-').
template <class celltype>
inline celltype CubicalBoundaryCell (const celltype &q, int i,
	bool onlyexisting)
{
	typedef typename celltype::CoordType coordtype;
	coordtype origleft [celltype::MaxDim];
	q. leftcoord (origleft);
	coordtype origright [celltype::MaxDim];
	q. rightcoord (origright);
	coordtype newcoord [celltype::MaxDim];
	int sd = q. spacedim ();
	int d = q. dim ();
	int count = 0;

	// if this is the first set of cells
	if (i < d)
	{
		for (int j = 0; j < sd; ++ j)
		{
			// copy the coordinates of the right vertex
			newcoord [j] = origleft [j];

			// modify the desired coordinate and finalize
			if (origleft [j] != origright [j])
			{
				if (i == count ++)
				{
					newcoord [j] = origright [j];
					for (j = j + 1; j < sd; ++ j)
						newcoord [j] = origleft [j];
					if (onlyexisting &&
						!celltype::PointBase::check
							(newcoord, sd))
						return q;
					return celltype (newcoord,
						origright, sd);
				}
			}
		}
		throw "False cubical cell's dimension.";
	}
	else
	{
		i -= d;
		for (int j = 0; j < sd; ++ j)
		{
			// copy the coordinates of the right vertex
			newcoord [j] = origright [j];

			// modify the desired coordinate and finalize
			if (origleft [j] != origright [j])
			{
				if (i == count ++)
				{
					newcoord [j] = origleft [j];
					for (j = j + 1; j < sd; j ++)
						newcoord [j] = origright [j];
					if (onlyexisting &&
						!celltype::PointBase::check
							(newcoord, sd))
						return q;
					return celltype (origleft,
						newcoord, sd);
				}
			}
		}
		throw "False dimension of a cubical cell.";
	}
} /* boundarycell */

/// Returns the i-th cell in the boundary of the given cell.
template <class celltype>
inline celltype CubicalBoundaryCell (const celltype &q, int i)
{
	return CubicalBoundaryCell (q, i, false);
} /* boundarycell */
	
/// Returns the length of the boundary of a cubical cell.
template <class celltype>
inline int CubicalBoundaryLength (const celltype &q)
{
	return q. dim () << 1;
} /* boundarylength */

/// Returns the i-th coefficient in the boundary of a cubical cell.
template <class celltype>
inline int CubicalBoundaryCoef (const celltype &q, int i)
{
	int d = q. dim ();
	if (i >= d)
		i -= d - 1;
	return (i & 1) ? 1 : -1;
} /* boundarycoef */


// --------------------------------------------------
// ---------------- CUBICAL CELL I/O ----------------
// --------------------------------------------------

/// Writes a cubical cell to the output stream in the text form.
/// The actual format depends on which OutputBits are set.
template <class celltype>
inline std::ostream &WriteCubicalCell (std::ostream &out, const celltype &c)
{
	// determine the data to be written
	typedef typename celltype::CoordType coordtype;
	coordtype lcoord [celltype::MaxDim];
	c. leftcoord (lcoord);
	int dim = c. spacedim ();
	coordtype rcoord [celltype::MaxDim];
	c. rightcoord (rcoord);

	if (celltype::OutputBits & celltype::BitProduct)
	{
		for (int i = 0; i < dim; ++ i)
		{
			out << '(';
			out << lcoord [i];
			if (rcoord [i] != lcoord [i])
				out << ',' << rcoord [i];
			out << ')';
			if (i < dim - 1)
				out << 'x';
		}
	}
	else
	{
		out << '[' << '(';
		int i;
		for (i = 0; i < dim; ++ i)
		{
			out << lcoord [i];
			if (i < dim - 1)
				out << ',';
		}
		out << ')';
		if (celltype::OutputBits & celltype::BitSpace)
			out << ' ';
		out << '(';
		for (i = 0; i < dim; ++ i)
		{
			out << rcoord [i];
			if (i < dim - 1)
				out << ',';
		}
		out << ')' << ']';
	}
	return out;
} /* operator << */

/// Reads a cubical cell form the input text stream. Allowed formats are:
/// (1) two opposite vertices: with minimal and maximal coordinates,
/// (2) a Cartesian product of intervals (with degenerated intervals
/// allowed),
/// (3) a full-dimensional cubical cell defined by its minimal vertex.
/// For example: [(1,8,-3) (2,9,-2)] = (1,2) x (8,9) x (-3,-2) = (1,8,-3).
/// Another example: [(-4,5,12) (-4,6,12)] = (-4) x (5,6) x (12).
/// Note that the definition of a cubical cell is interpreted
/// as the definition of a full-dimensional cube only if other
/// interpretations fail.
/// As a result, (3,4) will be treated as a 1-dimensional nondegenerated
/// cubical cell in R^1, and not as (3,4) x (4,5).
/// The same applies to 0-dimensional cells in R^1.
template <class celltype>
inline std::istream &ReadCubicalCell (std::istream &in, celltype &c)
{
	typedef typename celltype::CoordType coordtype;
	// make sure that an opening parenthesis is waiting in the input
	ignorecomments (in);
	int closing = closingparenthesis (in. peek ());
	if (closing == EOF)
		throw "Opening parenthesis expected while reading a cell.";

	// read the opening parenthesis
	in. get ();
	ignorecomments (in);

	// prepare the two vertices of a cubical cell
	coordtype c1 [celltype::MaxDim], c2 [celltype::MaxDim];

	// if there is another opening parenthesis...
	if (closingparenthesis (in. peek ()) != EOF)
	{
		// read coordinates of both vertices and a comma if any
		int dim1 = readcoordinates (in, c1, celltype::MaxDim);
		ignorecomments (in);
		if (in. peek () == ',')
		{
			in. get ();
			ignorecomments (in);
		}
		int dim2 = readcoordinates (in, c2, celltype::MaxDim);

		// read the closing bracket and verify that the data
		ignorecomments (in);
		if ((in. get () != closing) || (dim1 <= 0) || (dim1 != dim2))
			throw "Failed while reading two vertices of a cell.";

		// verify the distance between the vertices of the cell
		for (int i = 0; i < dim1; ++ i)
		{
			if ((c1 [i] != c2 [i]) && (c1 [i] + 1 != c2 [i]))
				throw "Vertices of a read cell are too far.";
		}

		// create the cubical cell with the given vertices and quit
		c = celltype (c1, c2, dim1);
		return in;
	}

	// try reading the first set of coordinates in the cell's definition
	coordtype c0 [celltype::MaxDim];
	int count = readcoordinates (in, c0, celltype::MaxDim, closing);
	if (count <= 0)
		throw "Can't read a cell.";
	ignorecomments (in);

	// if it looks like an interval, then read the cell as a product
	if ((count == 1) || (count == 2))
	{
		int dim = 0;
		c1 [dim] = c0 [0];
		c2 [dim ++] = c0 [count - 1];
		while ((in. peek () == 'x') || (in. peek () == 'X'))
		{
			in. get ();
			ignorecomments (in);
			count = readcoordinates (in, c0, celltype::MaxDim);
			ignorecomments (in);
			if ((count < 1) || (count > 2) ||
				(dim >= celltype::MaxDim))
				throw "Wrong interval while reading a cell.";
			if ((count == 2) && (c0 [1] != c0 [0]) &&
				(c0 [1] - c0 [0] != 1))
				throw "Too big interval defining a cell.";
			c1 [dim] = c0 [0];
			c2 [dim ++] = c0 [count - 1];
		}
		c = celltype (c1, c2, dim);
		return in;
	}

	// if the cell is defined as a full-dim. cube, create it this way
	for (int i = 0; i < count; ++ i)
		c1 [i] = c0 [i] + 1;
	c = celltype (c0, c1, count);
	return in;
} /* operator >> */


// --------------------------------------------------
// ----------- INTERSECTION OF TWO CUBES ------------
// --------------------------------------------------

/// Computes the left and right corner of a cell which is the intersection
/// of the two given cubes. Returns the actual dimension of this cell.
template<class coordtype>
inline int CommonCell (coordtype *left, coordtype *right,
	const coordtype *c1, const coordtype *c2, int spcdim,
	const coordtype *wrap = 0)
{
	// calculate the coordinates of both vertices of the cubical cell
	// and the dimension of the cubical cell
	int celldim = 0;
	for (int i = 0; i < spcdim; ++ i)
	{
		if (c1 [i] == c2 [i])
		{
			left [i] = c1 [i];
			right [i] = c1 [i];
			++ (right [i]);
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

	return celldim;
} /* CommonCell */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CELLMAIN_H_ 

/// @}

