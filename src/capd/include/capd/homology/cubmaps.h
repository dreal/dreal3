/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubmaps.h
///
/// This file contains some procedures defined for cubical maps.
/// These procedures are usually specializations of the generic ones
/// and support specific features of cubical maps.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: October 3, 2008.


#ifndef _CAPD_HOMOLOGY_CUBMAPS_H_ 
#define _CAPD_HOMOLOGY_CUBMAPS_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/gcomplex.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cube.h"
#include "capd/homology/cell.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {

// --------------------------------------------------
// ------------------- generators -------------------
// --------------------------------------------------

/// Writes projected homology generators of a cubical complex to a file.
/// Format: 0 = text format, 1 = chl format.
// Note: The main loop(s) of this function are copied from the function
// "createprojection".
template <class euclidom, class tCell>
std::ostream &writegenerators (std::ostream &out, const chain<euclidom> *hom,
	const chaincomplex<euclidom> &c, const gcomplex<tCell,euclidom> &g,
	const int *level, int xdim, int format = 0)
{
	typedef typename tCell::CoordType coordType;
	bool firstlist = true;
	for (int d = 0; d <= c. dim (); ++ d)
	{
		if ((level && !level [d]) || hom [d]. empty ())
			continue;
		if (firstlist)
			firstlist = false;
		else if (format == 0)
			out << '\n';
		if (format == 0)
		{
			if (hom [d]. size () == 1)
			{
				out << "The generator of H_" << d <<
					" follows:" << '\n';
			}
			else
			{
				out << "The " << hom [d]. size () <<
					" generators of H_" << d <<
					" follow:" << '\n';
			}
		}
		const hashedset<tCell> &cset = g [d];
		for (int_t i = 0; i < hom [d]. size (); ++ i)
		{
			if (format == 0)
			{
				if (hom [d]. size () > 1)
					out << "generator " <<
						(i + 1) << '\n';
			}
			const chain<euclidom> &lst =
				c. gethomgen (d, hom [d]. num (i));
			for (int_t j = 0; j < lst. size (); ++ j)
			{
				coordType left [tCell::MaxDim];
				cset [lst. num (j)]. leftcoord (left);
				coordType right [tCell::MaxDim];
				cset [lst. num (j)]. rightcoord (right);
				int projdim = 0;
				for (int k = 0; k < xdim; ++ k)
				{
					if (left [k] != right [k])
						++ projdim;
				}
				if (projdim != d)
					continue;
				if (format == 0)
				{
					out << lst. coef (j) << " * " <<
						tCell (left, right, xdim) <<
						'\n';
				}
				else
				{
					for (int k = 0; k < xdim; ++ k)
						out << left [k] << " ";
					for (int k = 0; k < xdim; ++ k)
						out << right [k] << " ";
					out << lst. coef (j) << " " <<
						(i + 1) << " " << d << '\n';
				}
			}
		}
	}
	return out;
} /* writegenerators */


// --------------------------------------------------
// ------------------- map images -------------------
// --------------------------------------------------

/// Creates images of cells in 'm' as unions of cubes determined
/// by f1 and f2. The domains of interest must be given explicitly.
/// Returns the total number of cubes in all the images of cells.
template <class euclidom, class tCell, class tCube>
int_t createimages (mvcellmap<tCell,euclidom,tCube> &m,
	const mvmap<tCube,tCube> &f1, const mvmap<tCube,tCube> &f2,
	const hashedset<tCube> &dom1, const hashedset<tCube> &dom2)
{
	typedef typename tCell::CoordType coordType;
	int_t countimages = 0;
	coordType leftbound [tCell::MaxDim];
	coordType rightbound [tCell::MaxDim];
	coordType left [tCell::MaxDim];
	coordType right [tCell::MaxDim];
	for (int d = 0; d <= m. dim (); ++ d)
	{
		const hashedset<tCell> &cset = m. get (d);
		if (cset. empty ())
			continue;
		const int spacedim = cset [0]. spacedim ();
		for (int_t i = 0; i < cset. size (); ++ i)
		{
			cset [i]. leftcoord (left);
			cset [i]. rightcoord (right);
			for (int_t j = 0; j < spacedim; ++ j)
			{
				// compensate for space wrapping
				if (right [j] < left [j])
					right [j] = left [j] + 1;
				// compute the bounds
				leftbound [j] = static_cast<coordType>
					(left [j] - (left [j] == right [j]));
				rightbound [j] = static_cast<coordType>
					(right [j] +
					(left [j] == right [j]));
			}
			tRectangle<coordType> r (leftbound, rightbound,
				spacedim);
			const coordType *c;
			while ((c = r. get ()) != NULL)
			{
				if (!tCube::PointBase::check (c, spacedim))
					continue;
				tCube q (c, spacedim);
				if (dom1. check (q))
					m. add (d, i, f1 (q));
				if (dom2. check (q))
					m. add (d, i, f2 (q));
			}
			countimages += m (cset [i]). size ();
		}
	}
	return countimages;
} /* createimages */

/// A wrapper for the above function if there is only one map.
template <class euclidom, class tCell, class tCube>
inline int_t createimages (mvcellmap<tCell,euclidom,tCube> &m,
	const mvmap<tCube,tCube> &f, const hashedset<tCube> &dom)
{
	mvmap<tCube,tCube> emptymap;
	hashedset<tCube> emptyset;
	return createimages (m, f, emptymap, dom, emptyset);
} /* createimages */

/// Creates images of cells in m as unions of cubes determined by f1 and f2.
/// Return the total number of cubes in all the images of cells.
template <class euclidom, class tCell, class tCube>
int_t createimages (mvcellmap<tCell,euclidom,tCube> &m,
	const mvmap<tCube,tCube> &f1, const mvmap<tCube,tCube> &f2)
{
	const hashedset<tCube> &dom1 = f1. getdomain ();
	const hashedset<tCube> &dom2 = f2. getdomain ();
	return createimages (m, f1, f2, dom1, dom2);
} /* createimages */

/// A wrapper for the above function if there is only one map.
template <class euclidom, class tCell, class tCube>
inline int_t createimages (mvcellmap<tCell,euclidom,tCube> &m,
	const mvmap<tCube,tCube> &f)
{
	mvmap<tCube,tCube> emptymap;
	return createimages (m, f, emptymap);
} /* createimages */


// --------------------------------------------------
// ------------------ projections -------------------
// --------------------------------------------------

/// Creates the chain map of the projection from a cell complex of the graph
/// of a map to a cell complex of the codomain of the map.
/// If a table of levels is given, creates the map only at given levels.
template <class euclidom, class tCell>
void createprojection (const gcomplex<tCell,euclidom> &Fcompl,
	const gcomplex<tCell,euclidom> &Ycompl,
	chainmap<euclidom> &cmap,
	int offset, int outdim, int discarddim, int *level = NULL)
{
	typedef typename tCell::CoordType coordType;
	// go through the list of all the dimensions which are of concern
	for (int d = 0; d <= Ycompl. dim (); ++ d)
	{
		if ((!level || level [d]) && (Fcompl. dim () >= d))
		{
			// take sets of cells of this dimension
			const hashedset<tCell> &Fset = Fcompl [d];
			if (Fset. empty ())
				continue;
			const hashedset<tCell> &Yset = Ycompl [d];
			if (Yset. empty ())
				continue;

			// go through the list of cells in Fcompl of dim. d
			for (int_t i = 0; i < Fset. size (); ++ i)
			{
				// get this cell and its coordinates
				const tCell &Fcell = Fset [i];
				coordType left [tCell::MaxDim];
				Fcell. leftcoord (left);
				coordType right [tCell::MaxDim];
				Fcell. rightcoord (right);

				// check if this cell has no width in the
				// directions that are discarded
				register int j;
				for (j = 0; j < offset; ++ j)
					if (left [j] != right [j])
					{
						j = offset + 33;
						break;
					}
				if (j > offset)
					continue;
				for (j = 0; j < discarddim; ++ j)
					if (left [offset + outdim + j] !=
						right [offset + outdim + j])
					{
						j = discarddim + 33;
						break;
					}
				if (j > discarddim)
					continue;

				// create the projected cell
				if (!(tCell::PointBase::check
					(left + offset, outdim)))
					continue;
				if (!(tCell::PointBase::check
					(right + offset, outdim)))
					continue;
			//	tCell projected (left + offset,
			//		right + offset, outdim);
				tCell projected (Fcell, offset, outdim);

				// find its number in Y
				int_t nr = Yset. getnumber (projected);

				// if not found, discard it
				if (nr < 0)
					continue;

				// add the pair to the projection map
				euclidom e;
				e = 1;
				cmap. add (d, nr, i, e);
			}
		}
	}
	return;
} /* createprojection */

/// Creates the image of the projection from the set of cubical cells in the
/// given geometric complex to the subspace of R^n spanned by the 'outdim'
/// subsequent standard vectors with the first number 'offset'.
/// Only these cells which appear in 'only' are added unless 'only' is empty.
template <class euclidom, class tCell>
void project (const gcomplex<tCell,euclidom> &c,
	gcomplex<tCell,euclidom> &img,
	const gcomplex<tCell,euclidom> &only,
	int offset, int outdim, int discarddim, const int *level,
	bool watchforimages)
{
	typedef typename tCell::CoordType coordType;

	// go through the list of all the dimensions which are of concern
	for (int d = 0; d <= c. dim (); ++ d)
	{
		if ((!level || level [d]) && (c. dim () >= d))
		{
			// take sets of cells of this dimension
			const hashedset<tCell> &cset = c [d];
			if (cset. empty ())
				continue;

			// go through the list of cells in c of dimension d
			for (int_t i = 0; i < cset. size (); ++ i)
			{
				// get this cell and its coordinates
				const tCell &thecell = cset [i];
				coordType left [tCell::MaxDim];
				thecell. leftcoord (left);
				coordType right [tCell::MaxDim];
				thecell. rightcoord (right);

				// check if this cell has no width in the
				// directions that are discarded
				int j;
				for (j = 0; j < offset; ++ j)
					if (left [j] != right [j])
					{
						j = offset + 33;
						break;
					}
				if (j > offset)
					continue;
				for (j = 0; j < discarddim; ++ j)
					if (left [offset + outdim + j] !=
						right [offset + outdim + j])
					{
						j = discarddim + 33;
						break;
					}
				if (j > discarddim)
					continue;

				// add the projected cell to the complex
				if (!(tCell::PointBase::check
					(left + offset, outdim))
					|| !(tCell::PointBase::check
					(right + offset, outdim)))
				{
					if (watchforimages)
						throw "Inclusion undefined!";
					else
						continue;
				}
				tCell projected (left + offset,
					right + offset, outdim);
				if ((only. dim () >= 0) &&
					!only. check (projected))
				{
					if (watchforimages)
						throw "Inclusion undefined.";
					else
						continue;
				}
				img. add (projected);
			}
		}
	}
	return;
} /* project */


// --------------------------------------------------
// ------------------- read cubes -------------------
// --------------------------------------------------

/// Reads the domain of a multivalued cubical map.
/// This is a specialization of the corresponding function
/// for reading the domain of a general multivalued map.
template <class tCube>
std::istream &readdomain (std::istream &in, hashedset<tCube> &dom)
{
	ignorecomments (in);
	if ((in. peek () != 'S') && (in. peek () != 's'))
	{
		mvmap<tCube,tCube> Fdummy;
		return readdomain (in, dom, Fdummy);
	}

	while (in. peek () != EOF)
	{
		if (in. peek () == '[')
		{
			in. get ();
			tCube q;
			in >> q;
			if (!in)
				throw "Can't read the file.";
			dom. add (q);
		}
		ignoreline (in);
		ignorecomments (in);
	}
	
	return in;
} /* readdomain */

/// Reads the image of a multivalued cubical map.
/// This is a specialization of the corresponding function
/// for reading the image of a general multivalued map.
template <class tCube>
std::istream &readimage (std::istream &in, hashedset<tCube> &img)
{
	ignorecomments (in);
	if ((in. peek () != 'S') && (in. peek () != 's'))
	{
		mvmap<tCube,tCube> Fdummy;
		return readimage (in, img, Fdummy);
	}

	typename tCube::CoordType left [tCube::MaxDim];
	typename tCube::CoordType right [tCube::MaxDim];
	while (in. peek () != EOF)
	{
		if (in. peek () == '[')
		{
			in. get ();
			tCube dummy;
			in >> dummy;
			in >> dummy;
			ignorecomments (in);
			in. get ();
			ignorecomments (in);
			in. get ();
			tCube q1, q2;
			in >> q1 >> q2;
			if (!in)
				throw "Can't read the file.";
			ignorecomments (in);
			in. get ();
			ignorecomments (in);
			int dim = q1. dim ();
			q1. coord (left);
			q2. coord (right);
			tRectangle<typename tCube::CoordType> r
				(left, right, dim);
			const typename tCube::CoordType *c;
			while ((c = r. get ()) != NULL)
				img. add (tCube (c, dim));
		}
		else
			ignoreline (in);
		ignorecomments (in);
	}

	return in;
} /* readimage */

/// Read the image of a set under a multivalued cubical map.
/// This is a specialization of the corresponding function
/// for reading the image of a general multivalued map.
template <class tCube>
std::istream &readimage (std::istream &in, const hashedset<tCube> &dom,
	hashedset<tCube> &img)
{
	ignorecomments (in);
	// the general format: [x,y,z] -> {[a,b,c], [d,e,f]}
	if ((in. peek () != 'S') && (in. peek () != 's'))
	{
		while (in. peek () != EOF)
		{
			if ((closingparenthesis (in. peek ()) == EOF) &&
				!std::isdigit (in. peek ()))
			{
				ignoreline (in);
				ignorecomments (in);
				continue;
			}
			tCube q;
			in >> q;
			bool ignore = !dom. check (q);
			ignorecomments (in);
			while (in. peek () == '-')
				in. get ();
			in. get (); // '>'
			ignorecomments (in);
			int opening = in. get ();
			int closing = closingparenthesis (opening);
			if (closing == EOF)
				throw "An opening brace '{' expected.";
			while ((in. peek () != EOF) &&
				(in. peek () != closing))
			{
				if (ignore)
				{
					if (in. get () == opening)
					{
						while ((in. peek () != EOF) &&
							(in. peek () != closing))
						{
							in. get ();
						}
						in. get (); // '}'
					}
				}
				else
				{
					in >> q;
					img. add (q);
					ignorecomments (in);
					if (in. peek () == ',')
					{
						in. get ();
						ignorecomments (in);
					}
				}
			}
		//	in. get (); // '}'
			ignoreline (in);
			ignorecomments (in);
		}
	}

	typename tCube::CoordType left [tCube::MaxDim];
	typename tCube::CoordType right [tCube::MaxDim];
	while (in. peek () != EOF)
	{
		if (in. peek () == '[')
		{
			in. get ();
			tCube domcube1, domcube2;
			in >> domcube1;
			if (!dom. check (domcube1))
			{
				ignoreline (in);
				ignorecomments (in);
				continue;
			}
			in >> domcube2;
			ignorecomments (in);
			in. get ();
			ignorecomments (in);
			in. get ();
			tCube q1, q2;
			in >> q1 >> q2;
			if (!in)
				throw "Can't read the file.";
			ignorecomments (in);
			in. get ();
			ignorecomments (in);
			if (dom. check (domcube1))
			{
				int dim = q1. dim ();
				q1. coord (left);
				q2. coord (right);
				tRectangle<typename tCube::CoordType> r
					(left, right, dim);
				const typename tCube::CoordType *c;
				while ((c = r. get ()) != NULL)
					img. add (tCube (c, dim));
			}
		}
		else
			ignoreline (in);
		ignorecomments (in);
	}

	return in;
} /* readimage */

/// Reads the restriction of a multivalued map to the given pair of sets.
template <class tCube>
std::istream &readselective (std::istream &in, const hashedset<tCube> &dom1,
	const hashedset<tCube> &dom2, mvmap<tCube,tCube> &m)
{
	if (dom1. empty () && dom2. empty ())
	{
		sout << "Warning: The domain of the map is empty.\n";
		return in;
	}

	ignorecomments (in);
	if ((in. peek () != 'S') && (in. peek () != 's'))
		return readselective (in, m, dom1, dom2);

	typename tCube::CoordType left [tCube::MaxDim];
	typename tCube::CoordType right [tCube::MaxDim];
	while (in. peek () != EOF)
	{
		if (in. peek () == '[')
		{
			in. get ();
			tCube domcube;
			in >> domcube;
			int dim = domcube. dim ();
			if (dom1. check (domcube) || dom2. check (domcube))
			{
				tCube q1, q2;
				in >> q1; // (ignored)
				ignorecomments (in);
				in. get ();
				ignorecomments (in);
				in. get ();
				in >> q1 >> q2;
				if (!in)
					throw "Can't read the file.";
				hashedset<tCube> &img = m [domcube];
				q1. coord (left);
				q2. coord (right);
				tRectangle<typename tCube::CoordType> r
					(left, right, dim);
				const typename tCube::CoordType *c;
				while ((c = r. get ()) != NULL)
					img. add (tCube (c, dim));
			}
		}
		ignoreline (in);
		ignorecomments (in);
	}

	return in;
} /* readselective */

/// Reads a restriction of a multivalued cubical map to the given set.
/// The order of arguments is reversed to distinguish form the template
/// defined for a general multivalued map.
template <class tCube>
inline std::istream &readselective (std::istream &in,
	const hashedset<tCube> &dom, mvmap<tCube,tCube> &m)
{
	hashedset<tCube> empty;
	return readselective (in, dom, empty, m);
} /* readselective */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CUBMAPS_H_ 

/// @}

