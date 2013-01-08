/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file gcomplex.h
///
/// This file contains a definition of a general geometric complex
/// which represents a polyhedron. It can be either a cubical complex,
/// a simplicial complex, or a general CW-complex. Several procedures
/// related to the homology computation are also implemented.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: January 23, 2010.


#ifndef _CAPD_HOMOLOGY_GCOMPLEX_H_ 
#define _CAPD_HOMOLOGY_GCOMPLEX_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/chains.h"
#include "capd/homology/gcomplex.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <cstdlib>

namespace capd {
namespace homology {


// class templates defined within this header file (in this order):
template <class cell, class euclidom>
class gcomplex;
template <class cell, class euclidom, class element>
class mvcellmap;


// --------------------------------------------------
// --------------- geometric complex ----------------
// --------------------------------------------------

template <class cell>
int boundarycoef (const cell &, int i);

template <class cell>
int boundarylength (const cell &);

template <class cell>
cell boundarycell (const cell &, int i);

/// The class that defines a geometric complex - a set of cells (cubes,
/// simplices, etc). Each cell has its dimension returned by the method
/// "dim ()" of the cell object. Additionally, the following functions
/// must be defined for the cell objects: "boundarylength (cell)" returns
/// the length of the boundary of a cell (i.e., the number of
/// lower-dimensional cells in its boundary), "boundarycell (cell, i)"
/// returns the i-th cell in the boundary, and "boundarycoef (cell, i)"
/// returns the i-th integer coefficient in the boundary.
template <class cell, class euclidom>
class gcomplex
{
public:
	/// The default constructor.
	gcomplex ();

	/// The copy constructor.
	gcomplex (const gcomplex<cell,euclidom> &c);

	/// The destructor.
	~gcomplex ();

	/// The assignment operator.
	gcomplex &operator = (const gcomplex<cell,euclidom> &c);

	/// Returns the dimension of the complex, that is, the highest
	/// dimension of any cell contained in the complex.
	int dim () const;

	/// Returns the number of cells in the complex.
	int_t size () const;

	/// Returns 'true' iff the cell complex is empty.
	bool empty () const;

	/// Returns the set of cells of the given dimension.
	const hashedset<cell> &operator [] (int d) const;

	/// Returns the coboundary of the given cell.
	const hashedset<cell> &getcob (const cell &c) const;

	/// Returns the coboundary of the given cell.
	/// The dimension of the cell must be given.
	const hashedset<cell> &getcob (const cell &c, int d) const;

	/// Add a cell to the geometric complex.
	gcomplex<cell,euclidom> &add (const cell &c);

	/// Adds a set of cells to the geometric complex.
	/// It is assumed that all the cells have dimension d.
	gcomplex<cell,euclidom> &add (const hashedset<cell> &c, int d);

	/// Adds a set of cells to the geometric complex.
	gcomplex<cell,euclidom> &add (const hashedset<cell> &c);

	/// Adds all the cells from a geometric complex.
	gcomplex<cell,euclidom> &add (const gcomplex<cell,euclidom> &c);

	/// Remove a cell from the geometric complex.
	gcomplex<cell,euclidom> &remove (const cell &c);

	/// Removes a set of cells to the geometric complex.
	/// It is assumed that all the cells have dimension d.
	gcomplex<cell,euclidom> &remove (const hashedset<cell> &c, int d);

	/// Removes a set of cells to the geometric complex.
	gcomplex<cell,euclidom> &remove (const hashedset<cell> &c);

	/// Adds all the cells from a geometric complex.
	gcomplex<cell,euclidom> &remove (const gcomplex<cell,euclidom> &c);

	/// Remove all the cells of the given dimension.
	gcomplex<cell,euclidom> &removeall (int d);

	/// Check whether the given cell is in the complex.
	/// Returns true if yes, false if not.
	bool check (const cell &c) const;

	/// Adds boundaries of all the cells of given dimension to the
	/// geometric complex. If requested, keeps the information
	/// about the coboundaries. Returns the number of cells added.
	int_t addboundaries (int d, bool addcob = false);

	/// Adds boundaries of all the cells of all dimensions to the
	/// geometric complex. If requested, keeps the information
	/// about the coboundaries. Returns the number of cells added.
	int_t addboundaries (bool addcob = false);

	/// Adds boundaries of all the cells of given dimension to the
	/// geometric complex, except for the cells which belong to the
	/// geometric complex "notthese". If "keepused" is set to false,
	/// then cells whose boundaries have been added are removed from
	/// the geometric complex; otherwise, they are kept there.
	/// Returns the number of cells added.
	int_t addboundaries (int d, gcomplex<cell,euclidom> &notthese,
		bool keepused = false);

	/// Adds boundaries of all the cells of all dimensions to the
	/// geometric complex, except for the cells which belong to the
	/// geometric complex "notthese". If "keepused" is set to false,
	/// then cells whose boundaries have been added are removed from
	/// the geometric complex; otherwise, they are kept there.
	/// Returns the number of cells added.
	int_t addboundaries (gcomplex<cell,euclidom> &notthese,
		bool keepused = false);

	/// Adds boundaries and also fills in the given chain complex.
	int_t addboundaries (int d, chaincomplex<euclidom> &c);

	/// Adds boundaries and also fills in the given chain complex.
	int_t addboundaries (chaincomplex<euclidom> &c);

	/// Adds boundaries and also fills in the given chain complex.
	int_t addboundaries (int d, chaincomplex<euclidom> &c,
		gcomplex<cell,euclidom> &notthese,
		bool keepused = false);

	/// Adds boundaries and also fills in the given chain complex.
	int_t addboundaries (chaincomplex<euclidom> &c,
		gcomplex<cell,euclidom> &notthese,
		bool keepused = false);

	/// The actual function that is used for all the functions
	/// for adding boundaries of a fixed dimension.
	int_t addboundaries (int d, chaincomplex<euclidom> *c,
		gcomplex<cell,euclidom> *notthese,
		bool dontadd, bool keepused, bool addcob);

	/// The actual function that is used for all the functions
	/// for adding boundaries of all dimensions.
	int_t addboundaries (chaincomplex<euclidom> *c,
		gcomplex<cell,euclidom> *notthese,
		bool dontadd, bool keepused, bool addcob);

	/// Adds boundaries of all the cells of the given dimension
	/// and then performs free face collapses.
	/// Does not remove cells listed in 'keep'.
	/// Removes from 'other' and 'this' unnecessary d-dim cells.
	/// Returns the number of collapses performed.
	int_t collapse (int d,
		gcomplex<cell,euclidom> &other,
		const gcomplex<cell,euclidom> &keep,
		bool addbd, bool addcob, bool disjoint,
		bool quiet = false);

	/// Adds boundaries to 'other' and 'keep', and then does
	/// the free face collapses.
	/// Does this at all levels or only the necessary ones.
	/// Remove sfrom 'other' cells that are not in the result.
	/// If 'disjoint', then removes 'other' from 'this'.
	/// Removes from 'keep' cells not contained in the result.
	/// Returns the number of collapses performed.
	int_t collapse (gcomplex<cell,euclidom> &other,
		gcomplex<cell,euclidom> &keep,
		bool addbd, bool addcob, bool disjoint,
		const int *level = NULL, bool quiet = false);

private:
	/// The tables with cells of dimension 0, 1, 2, etc.
	hashedset<cell> **tab;

	/// The tables with coboundaries of cells of these dimensions.
	mvmap<cell,cell> **cob;

	/// The number of tables.
	int n;

	/// Increases the dimension of the complex to take this cell.
	void increasedimension (int d);

	/// Frees empty sets if there are no cells of high dimensions.
	void decreasedimension ();

}; /* class gcomplex */

// --------------------------------------------------

template <class cell, class euclidom>
inline gcomplex<cell,euclidom>::gcomplex (): tab (NULL), cob (NULL), n (0)
{
	return;
} /* gcomplex<cell,euclidom>::gcomplex */

template <class cell, class euclidom>
gcomplex<cell,euclidom>::gcomplex (const gcomplex<cell,euclidom> &c)
{
	n = c. n;
	if (n > 0)
	{
		tab = new hashedset<cell> *[n];
		cob = new mvmap<cell,cell> *[n];
		if (!tab || !cob)
			throw "Cannot copy a geometric complex.";
	}
	else
	{
		tab = NULL;
		cob = NULL;
	}
	for (int i = 0; i < n; ++ i)
	{
		tab [i] = new hashedset<cell> (*(c. tab [i]));
		cob [i] = new mvmap<cell,cell> (*(c. cob [i]));
		if (!tab [i] || !cob [i])
			throw "Cannot copy part of a geometric complex.";
	}
	return;
} /* gcomplex<cell,euclidom>::gcomplex */

template <class cell, class euclidom>
gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::operator =
	(const gcomplex<cell,euclidom> &c)
{
	// if the sizes of the tables are not the same, re-allocate the table
	// and use the copying constructor to create an identical table
	if (n != c. n)
	{
		if (tab)
		{
			for (int i = 0; i < n; ++ i)
				delete tab [i];
			delete [] tab;
		}
		if (cob)
		{
			for (int i = 0; i < n; ++ i)
				delete cob [i];
			delete [] cob;
		}
		n = c. n;
		if (n > 0)
		{
			tab = new hashedset<cell> *[n];
			cob = new mvmap<cell,cell> *[n];
			if (!tab || !cob)
				throw "Cannot copy a geometric complex.";
		}
		else
		{
			tab = NULL;
			cob = NULL;
		}
		for (int i = 0; i < n; ++ i)
		{
			tab [i] = new hashedset<cell> (*(c. tab [i]));
			cob [i] = new mvmap<cell,cell> (*(c. cob [i]));
			if (!tab [i] || !cob [i])
				throw "Cannot copy part of a geom. complex.";
		}
	}
	// otherwise copy the source table to this complex
	else
	{
		for (int i = 0; i < n; ++ i)
		{
			*(tab [i]) = *(c. tab [i]);
			*(cob [i]) = *(c. cob [i]);
		}
	}
	return *this;
} /* gcomplex<cell,euclidom>::operator = */

template <class cell, class euclidom>
gcomplex<cell,euclidom>::~gcomplex ()
{
	for (int i = 0; i < n; ++ i)
	{
		if (tab [i])
			delete tab [i];
		if (cob [i])
			delete cob [i];
	}
	if (tab)
		delete [] tab;
	if (cob)
		delete [] cob;
	return;
} /* gcomplex<cell,euclidom>::~gcomplex */

template <class cell, class euclidom>
inline int gcomplex<cell,euclidom>::dim () const
{
	return n - 1;
} /* gcomplex<cell,euclidom>::dim */

template <class cell, class euclidom>
int_t gcomplex<cell,euclidom>::size () const
{
	int_t count = 0;
	for (int i = 0; i < n; ++ i)
		count += tab [i] -> size ();
	return count;
} /* gcomplex<cell,euclidom>::size */

template <class cell, class euclidom>
bool gcomplex<cell,euclidom>::empty () const
{
	if (!n)
		return true;
	for (int i = 0; i < n; ++ i)
		if (!(*(tab [i])). empty ())
			return false;
	return true;
} /* gcomplex<cell,euclidom>::empty */

template <class cell, class euclidom>
inline const hashedset<cell> &gcomplex<cell,euclidom>::operator [] (int d)
	const
{
	if ((d < 0) || (d >= n))
		throw "Dimension out of range for retrieving cells.";
	return *(tab [d]);
} /* gcomplex<cell,euclidom>::operator [] */

template <class cell, class euclidom>
inline const hashedset<cell> &gcomplex<cell,euclidom>::getcob (const cell &c)
	const
{
	return getcob (c, c. dim ());
} /* gcomplex<cell,euclidom>::getcob */

template <class cell, class euclidom>
inline const hashedset<cell> &gcomplex<cell,euclidom>::getcob (const cell &c,
	int d) const
{
	if ((d < 0) || (d >= n))
		throw "Dimension out of range for coboundary.";
	return (*(cob [d])) (c);
} /* gcomplex<cell,euclidom>::getcob */

template <class cell, class euclidom>
inline gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::add (const cell &c)
{
	// get the dimension of the cell
	int d = c. dim ();
	if (d < 0)
		throw "Negative dimension of a cell to be added.";

	// if the dimension of the cell is beyond the allocated table,
	// then increase the table
	if (n <= d)
		increasedimension (d);

	// add the cell to the suitable set of cells
	tab [d] -> add (c);

	return *this;
} /* gcomplex<cell,euclidom>::add */

template <class cell, class euclidom>
inline gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::add
	(const hashedset<cell> &c, int d)
{
	// increase the dimension of the complex if necessary
	if (d > n)
		increasedimension (d);

	// add the set of cells to the suitable set
	tab [d] -> add (c);

	return *this;
} /* gcomplex<cell,euclidom>::add */

template <class cell, class euclidom>
gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::add
	(const hashedset<cell> &c)
{
	int_t size = c. size ();
	for (int_t i = 0; i < size; ++ i)
		add (c [i]);

	return *this;
} /* gcomplex<cell,euclidom>::add */

template <class cell, class euclidom>
gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::add
	(const gcomplex<cell,euclidom> &c)
{
	// increase the dimension of the complex if necessary
	if (c. n > n)
		increasedimension (c. dim ());

	// add the sets of cells
	for (int i = 0; i < c. n; ++ i)
	{
		tab [i] -> add (*(c. tab [i]));
	/*	const hashedset<cell> &cset = *(c. tab [i]);
		for (int j = 0; j < cset. size (); ++ j)
		{
			const cell &thecell = cset [j];
			tab [i] -> add (thecell);
			if (cob && c. cob)
				(*(cob [i])) [thecell] =
					((*(c. cob [i])) (thecell));
		}
	*/
	}

	return *this;
} /* gcomplex<cell,euclidom>::add */

template <class cell, class euclidom>
inline gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::remove
	(const cell &c)
{
	// get the dimension of the cell
	int d = c. dim ();
	if (d < 0)
		throw "Negative dimension of a cell to be removed.";

	// if the dimension of the cell is beyond the allocated table,
	// then ignore it
	if (n <= d)
		return *this;

	// remove the cell from the suitable set of cells
	tab [d] -> remove (c);

	// decrease the dimension of the complex if no cells remain
	if ((d == n - 1) && tab [d] -> empty ())
		decreasedimension ();

	return *this;
} /* gcomplex<cell,euclidom>::remove */

template <class cell, class euclidom>
gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::remove
	(const gcomplex<cell,euclidom> &c)
{
	// figure out the number of tables to work on
	int m = c. n;
	if (m > n)
		m = n;

	// remove the sets of cells
	for (int i = 0; i < m; ++ i)
		tab [i] -> remove (*(c. tab [i]));

	// decrease the dimension of the complex if no highdim cells remain
	decreasedimension ();

	return *this;
} /* gcomplex<cell,euclidom>::remove */

template <class cell, class euclidom>
inline gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::remove
	(const hashedset<cell> &c, int d)
{
	// remove the set of cells to the suitable set
	tab [d] -> remove (c);

	// decrease the dimension of the complex if no highdim cells remain
	decreasedimension ();

	return *this;
} /* gcomplex<cell,euclidom>::remove */

template <class cell, class euclidom>
gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::remove
	(const hashedset<cell> &c)
{
	int_t size = c. size ();
	for (int_t i = 0; i < size; ++ i)
		remove (c [i]);

	return *this;
} /* gcomplex<cell,euclidom>::remove */

template <class cell, class euclidom>
gcomplex<cell,euclidom> &gcomplex<cell,euclidom>::removeall (int d)
{
	if (d == n - 1)
	{
		-- n;
		delete tab [n];
		delete cob [n];
		decreasedimension ();
	}
	else if ((d >= 0) && (d < n))
	{
		delete tab [d];
		tab [d] = new hashedset<cell>;
	}

	return *this;
} /* gcomplex<cell,euclidom>::removeall */

template <class cell, class euclidom>
bool gcomplex<cell,euclidom>::check (const cell &c) const
{
	// get the dimension of the cell
	int d = c. dim ();
	if (d < 0)
		throw "Negative dimension of a cell to be checked.";

	// if the dimension of the cell is beyond the allocated table,
	// then it is not there
	if (n <= d)
		return false;

	// check for the existence of the cell in the suitable set of cells
	return tab [d] -> check (c);
} /* gcomplex<cell,euclidom>::check */

template <class cell, class euclidom>
int_t gcomplex<cell,euclidom>::addboundaries (int d,
	chaincomplex<euclidom> *c, gcomplex<cell,euclidom> *notthese,
	bool dontadd, bool keepused, bool addcob)
{
	// if the dimension is inappropriate, do nothing
	if ((d <= 0) || (d >= n))
		return 0;

	// first add boundaries to the other cell complex
	if (notthese && !dontadd)
		notthese -> addboundaries (d);

	int_t prevsize = tab [d - 1] -> size ();
	hashedset<cell> &cset = *(tab [d]);
	for (int_t i = 0; i < cset. size (); ++ i)
	{
		const cell &thecell = cset [i];
		int len = boundarylength (thecell);
		for (int j = 0; j < len; ++ j)
		{
			// take the j-th boundary cell
			cell bcell = boundarycell (thecell, j);

			// add it to the cell complex unless it is unwanted
			if (!notthese || !notthese -> check (bcell))
			{
				tab [d - 1] -> add (bcell);
				if (c)
				{
					int icoef = boundarycoef (thecell, j);
					euclidom coef;
					if (icoef < 0)
					{
						coef = -icoef;
						coef = -coef;
					}
					else
						coef = icoef;
					c -> add (d, tab [d - 1] ->
						getnumber (bcell), i, coef);
				}
				if (addcob)
					(*(cob [d - 1])) [bcell].
						add (thecell);
			}
		}
	}

	// clean the used level in 'notthese'
	if (notthese && !keepused)
		notthese -> removeall (d);

	return tab [d - 1] -> size () - prevsize;
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
int_t gcomplex<cell,euclidom>::addboundaries (chaincomplex<euclidom> *c,
	gcomplex<cell,euclidom> *notthese, bool dontadd, bool keepused,
	bool addcob)
{
	int_t countadded = 0;
	for (int d = n - 1; d > 0; -- d)
		countadded += addboundaries (d, c, notthese,
			dontadd, keepused, addcob);
	return countadded;
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
inline int_t gcomplex<cell,euclidom>::addboundaries (int d, bool addcob)
{
	return addboundaries (d, NULL, NULL, false, false, addcob);
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
inline int_t gcomplex<cell,euclidom>::addboundaries (bool addcob)
{
	return addboundaries (NULL, NULL, false, false, addcob);
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
inline int_t gcomplex<cell,euclidom>::addboundaries (int d,
	gcomplex<cell,euclidom> &notthese, bool keepused)
{
	return addboundaries (d, NULL, &notthese, false, keepused, false);
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
int_t gcomplex<cell,euclidom>::addboundaries
	(gcomplex<cell,euclidom> &notthese, bool keepused)
{
	return addboundaries (NULL, &notthese, false, keepused, false);
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
inline int_t gcomplex<cell,euclidom>::addboundaries (int d,
	chaincomplex<euclidom> &c)
{
	return addboundaries (d, &c, NULL, false, false, false);
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
inline int_t gcomplex<cell,euclidom>::addboundaries (chaincomplex<euclidom> &c)
{
	return addboundaries (&c, NULL, false, false, false);
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
inline int_t gcomplex<cell,euclidom>::addboundaries (int d,
	chaincomplex<euclidom> &c, gcomplex<cell,euclidom> &notthese,
	bool keepused)
{
	return addboundaries (d, &c, &notthese, false, keepused, false);
} /* gcomplex<cell,euclidom>::addboundaries */

template <class cell, class euclidom>
inline int_t gcomplex<cell,euclidom>::addboundaries (chaincomplex<euclidom> &c,
	gcomplex<cell,euclidom> &notthese, bool keepused)
{
	return addboundaries (&c, &notthese, false, keepused, false);
} /* gcomplex<cell,euclidom>::addboundaries */

// --------------------------------------------------

/// Finds the given element in the table of given length.
/// Return its index or -1 if not found.
template <class element>
int_t findelem (const multitable<element> &tab, const element &e, int_t len)
{
	if (len <= 0)
		return -1;

	// prepare a random search starting point and step increase
	int_t i = static_cast<int_t> (std::rand ()) % len;
	if (i < 0)
		i = static_cast<int_t> (1) - i;
	int_t step = static_cast<int_t> (std::rand () + 17) % len;
	if (step < 0)
		step = static_cast<int_t> (1) - step;
	if (step < 17)
		step = 17;
	if (step > len)
		step = len >> 1;
	if (step < 1)
		step = 1;

	// jump randomly in the table to find some element if possible
	int_t jumping = len >> 1;
	while (jumping --)
	{
	//	if ((i < 0) || (i >= len))
	//		throw "Wrong random number.";
		if (tab (i) == e)
			return i;
	//	if ((i + 1 < len) && (tab (i + 1) == e))
	//		return i + 1;
		if (jumping)
		{
			i += step;
			if (i >= len)
				i -= len;
		}
	}

	// if not found, try finding the element thoroughly
	for (int_t i = 0; i < len; ++ i)
	{
		if (tab (i) == e)
			return i;
	}
	return -1;
} /* findelem */

template <class cell, class euclidom>
int_t gcomplex<cell,euclidom>::collapse (int d,
	gcomplex<cell,euclidom> &other, const gcomplex<cell,euclidom> &keep,
	bool addbd, bool addcob, bool disjoint, bool quiet)
{
	if ((d <= 0) || (d > dim ()))
		return 0;

	// prepare references to the sets of cells of interest
	hashedset<cell> &cset = *(tab [d]);
	hashedset<cell> &bset = *(tab [d - 1]);
	hashedset<cell> empty;
	hashedset<cell> &cother = (other. dim () >= d) ?
		*(other. tab [d]) : empty;
	hashedset<cell> &bother = (other. dim () >= d - 1) ?
		*(other. tab [d - 1]) : empty;
	const hashedset<cell> &ckeep = (keep. dim () >= d) ?
		*(keep. tab [d]) : empty;
	const hashedset<cell> &bkeep = (keep. dim () >= d - 1) ?
		*(keep. tab [d - 1]) : empty;

	// show the currently processed dimension
	if (!quiet)
	{
		if (d > 9)
			scon << "#\b";
		else
			scon << d << '\b';
	}

	// go through all the cells from A and generate their boundaries
	if (addbd)
	{
		if (!quiet)
		{
			sseq << "\"Adding boundaries of cells in A...\"\n";
			sseq << "D 0\n";
		}
		for (int_t i = 0; i < cother. size (); ++ i)
		{
			// select the given cell in 'cother'
			const cell &thecell = cother [i];

			// detect the length of the boundary of this cell
			int blen = boundarylength (thecell);

			// add to 'bother' all the cells in this boundary
			for (int j = 0; j < blen; ++ j)
				bother. add (boundarycell (thecell, j));

			// write the boundary cells to the sequential file
			if (!quiet && (sseq. show || sseq. log))
			{
				for (int j = 0; j < blen; ++ j)
					sseq << '2' << boundarycell
						(thecell, j) << '\n';
			}
		}
	}
	if (!quiet)
		sseq << "D 100\n";

	// if the complexes should be disjoint, remove 'bother' from 'bset'
	if (disjoint)
		bset. remove (bother);

	// prepare tables for coboundaries of cells in X and their lengths
	multitable<int> coblen;
	multitable<hashedset <cell> > coboundary;
	if (!bset. empty ())
		coblen. fill (0, bset. size ());

	// go through the list of all the cells of dimension 'd' in the set,
	// add their boundaries to 'bset' and create the coboundary links;
	// note: these cells may appear in the 'other' complex
	if (!quiet)
		sseq << "\"Adding boundaries of cells of dimension " <<
			d << "\"\nD 0\n";
	bool maximal = (d == dim ());
	for (int_t i = 0; i < cset. size (); ++ i)
	{
		// select the i-th d-dimensional cell
		const cell &thecell = cset [i];

		// check if this cell belongs to 'cother'
		bool cbelongs = cother. check (thecell);

		// if this cell should be removed, do it
		if (cbelongs && (disjoint || maximal))
		{
		//	if (!quiet && (sseq. show || sseq. log))
		//		sseq << '0' << thecell << '\n';
			cother. remove (thecell);
			cset. removenum (i --);
			continue;
		}

		// detect the length of the boundary of this cell
		int blen = boundarylength (thecell);

		// should this cell be kept secure from the collapses?
		bool keepit = ckeep. check (thecell);

		// go through all the cells in this boundary
		for (int j = 0; j < blen; ++ j)
		{
			// take the j-th boundary cell
			cell bcell = boundarycell (thecell, j);

			// check if this cell belongs to the other complex
			bool bbelongs = bother. check (bcell);

			// if it is in 'bother', then skip it if disjoint
			if (bbelongs && disjoint)
				continue;

			// add this cell to 'bset' or get its number
			int_t prev = bset. size ();
			int_t number = addbd ? bset. add (bcell) :
				bset. getnumber (bcell);

			// if the cell is not there, skip it
			if (number < 0)
				continue;

			// if this is the first occurrence of the cell
			if ((prev < bset. size ()) || (coblen [number] == 0))
			{
				// write it to the sequence if necessary
				if (!quiet && !bbelongs)
					sseq << '1' << bcell << '\n';

				// if this cell should be kept, mark it
				if (keepit || bkeep. check (bset [number]) ||
					bother. check (bset [number]))
					coblen [number] = 13;
				else
					coblen [number] = 1;
				coboundary [number]. add (thecell);
			}

			// otherwise add the corresponding coboundary link
			else
			{
				++ (coblen [number]);
				coboundary [number]. add (thecell);
			}
		}
	}
	if (!quiet)
		sseq << "D 100\n";

	// show a dot
	if (!quiet)
		scon << "*\b";

	// prepare tables for cells to be removed
	hashedset<cell> cremove, bremove;
	int_t nremove = 0;

	// go through all the free faces
	if (!quiet)
		sseq << "\"Collapsing free faces...\"\n";
	while (1)
	{
		// find a free face
		int_t ncell = findelem (coblen, 1, bset. size ());

		// if not found then finish
		if (ncell < 0)
			break;

		// collapse this cell with its parent cell
		const cell &parent = coboundary [ncell] [0];
		int blen = boundarylength (parent);
		coblen [ncell] = 0;

		// remove the parent cell from coboundaries
		for (int j = 0; j < blen; ++ j)
		{
			cell thecell = boundarycell (parent, j);
			int_t number = bset. getnumber (thecell);
			if ((number >= 0) && (coblen [number] > 0))
			{
				coboundary [number]. remove (parent);
				-- (coblen [number]);
			}
		}

		// write these cells to the sequence file
		if (!quiet)
		{
			sseq << '0' << bset [ncell] << '\n';
			sseq << '0' << parent << '\n';
		}

		// mark these cells for removal
		cremove. add (parent);
		bremove. add (bset [ncell]);
		++ nremove;

		// clear the coboundary, because it is no longer used
		coboundary [ncell] = empty;
	}

	// add the computed coboundaries if required
	if (addcob)
	{
		for (int_t i = 0; i < bset. size (); ++ i)
			if (!bremove. check (bset [i]))
			{
				coboundary [i]. remove (cremove);
				(*(cob [d - 1])) [bset [i]]. add
					(coboundary [i]);
			}
	}

	// remove cells that are scheduled for removal from 'cset'
	if (nremove == cset. size ())
	{
		removeall (d);
		other. removeall (d);
	}
	else
	{
		for (int_t i = 0; i < nremove; ++ i)
			cset. remove (cremove [i]);
	}

	// remove from the set of boundary cells these scheduled for removal
	for (int_t i = 0; i < nremove; ++ i)
		bset. remove (bremove [i]);

	// update the dimension of the cell complex - is this necessary?
	decreasedimension ();

	// show a dot
	if (!quiet)
		scon << '.';

	return nremove;
} /* gcomplex<cell,euclidom>::collapse */

template <class cell, class euclidom>
int_t gcomplex<cell,euclidom>::collapse (gcomplex<cell,euclidom> &other,
	gcomplex<cell,euclidom> &keep, bool addbd, bool addcob,
	bool disjoint, const int *level, bool quiet)
{
	// determine the lower bound for the adding boundaries levels
	int dmin = 0;
	if (level)
	{
		while ((dmin < dim ()) && (!level [dmin]))
			++ dmin;
		if (dmin && level [dmin])
			-- dmin;
	}

	// add boundaries to high-dimensional cells in 'keep'
	while (keep. dim () > dim ())
	{
		keep. addboundaries (keep. dim ());
		keep. removeall (keep. dim ());
	}

	// add boundaries to high-dimensional cells in 'other'
	if (other. dim () > dim ())
	{
		other. addboundaries (other. dim ());
		other. removeall (other. dim ());
	}

	// add boundaries and collapse in all the dimensions of interest
	int_t counter = 0;
	for (int d = dim (); d > dmin; -- d)
	{
		// add boundaries to the other cell complexes
		keep. addboundaries (d);

		// add boundaries and collapse this level
		counter += collapse (d, other, keep, addbd, addcob, disjoint,
			quiet);

		// remove unnecessary cells from 'other'
		if (disjoint)
			other. removeall (d);

		// remove unnecessary cells from 'keep'
		keep. removeall (d);
	}

	// forget all the other cells of minimal dimension which are not used
	if (!disjoint && (dim () >= dmin) && (other. dim () >= dmin))
	{
		hashedset<cell> &cset = *(tab [dmin]);
		hashedset<cell> &cother = *(other. tab [dmin]);
		for (int_t i = 0; i < cother. size (); ++ i)
		{
			if (!(cset. check (cother [i])))
				cother. removenum (i --);
		}
	}

	// remove unused cells which were supposed to be kept
	if (!keep. empty ())
	{
		gcomplex<cell,euclidom> empty;
		keep = empty;
	}

	if (!quiet)
		scon << ' ';

	return counter;
} /* gcomplex<cell,euclidom>::collapse */

template <class cell, class euclidom>
void gcomplex<cell,euclidom>::increasedimension (int d)
{
	// create a new table for sets of cells
	hashedset<cell> **newtab = new hashedset<cell> *[d + 1];
	mvmap<cell,cell> **newcob = new mvmap<cell,cell> *[d + 1];

	// copy anything that was in the old table
	for (int i = 0; i < n; ++ i)
	{
		newtab [i] = tab [i];
		newcob [i] = cob [i];
	}

	// delete the old table if it was allocated
	if (tab)
		delete [] tab;
	if (cob)
		delete [] cob;

	// initialize the remaining portion of the new table
	tab = newtab;
	cob = newcob;
	for (int i = n; i < d + 1; ++ i)
	{
		tab [i] = new hashedset<cell>;
		cob [i] = new mvmap<cell,cell>;
	}

	// set the new dimension
	n = d + 1;

	return;
} /* gcomplex<cell,euclidom>::increasedimension */

template <class cell, class euclidom>
void gcomplex<cell,euclidom>::decreasedimension ()
{
	while (n && tab [n - 1] -> empty ())
	{
		-- n;
		delete tab [n];
		delete cob [n];
	}
	if (!n)
	{
		delete [] tab;
		tab = NULL;
		delete [] cob;
		cob = NULL;
	}
	return;
} /* gcomplex<cell,euclidom>::decreasedimension */

// --------------------------------------------------

/// Creates an algebraic chain complex based on the data from the given
/// geometric cell complex.
/// Boundary formulas are restricted to cells which are in the geom. complex.
/// The chain complex should already be initialized with the right dimension.
template <class cell, class euclidom>
chaincomplex<euclidom> &createchaincomplex (chaincomplex<euclidom> &c,
	const gcomplex<cell,euclidom> &g, bool quiet = false)
{
	if (g. dim () < 0)
		return c;
	c. def_gen (0, g [0]. size ());
	for (int d = 1; d <= g. dim (); ++ d)
	{
		c. def_gen (d, g [d]. size ());
		for (int_t i = 0; i < g [d]. size (); ++ i)
		{
			int len = boundarylength (g [d] [i]);
			for (int j = 0; j < len; ++ j)
			{
				// take the j-th boundary cell
				cell thecell = boundarycell (g [d] [i], j);
	
				// add it to the chain complex
				if (g. check (thecell))
				{
					int icoef = boundarycoef
						(g [d] [i], j);
					euclidom coef;
					if (icoef < 0)
					{
						coef = -icoef;
						coef = -coef;
					}
					else
						coef = icoef;
					c. add (d, g [d - 1]. getnumber
						(thecell), i, coef);
				}
			}
		}
		if (!quiet)
		{
			if (d < g. dim ())
				scon << '.';
			else
				scon << ". ";
		}
	}
	return c;
} /* createchaincomplex */

/// Writes out a chain complex of the geometric cell complex.
/// Boundary formulas are restricted to cells which are in the geom. complex.
/// If symbolic names requested, the cells are written directly
/// as generators.
/// This procedure is a slightly modified version of "createchaincomplex".
template <class cell, class euclidom>
std::ostream &writechaincomplex (std::ostream &out,
	const gcomplex<cell,euclidom> &g, bool symbolicnames = false,
	bool quiet = false)
{
	if (g. dim () < 0)
		return out;
	out << "chaincomplex\n\n";
	out << "maxdimension " << g. dim () << "\n\n";
	out << "dimension 0: " << g [0]. size () << "\n\n";
	for (int d = 1; d <= g. dim (); ++ d)
	{
		out << "dimension " << d << ": " << g [d]. size () << "\n";
		for (int_t i = 0; i < g [d]. size (); ++ i)
		{
			bool cellwritten = false;
			int len = boundarylength (g [d] [i]);
			for (int j = 0; j < len; ++ j)
			{
				// take the j-th boundary cell
				cell thecell = boundarycell (g [d] [i], j);

				// add it to the chain complex
				if (g. check (thecell))
				{
					int icoef = boundarycoef
						(g [d] [i], j);
					euclidom coef;
					if (icoef < 0)
					{
						coef = -icoef;
						coef = -coef;
					}
					else
						coef = icoef;
					if (!cellwritten)
					{
						out << "\t# ";
						if (symbolicnames)
							out << g [d] [i];
						else
							out << (i + 1);
						out << " = ";
						if (-coef == 1)
							out << "- ";
					}
					else if (coef == 1)
						out << " + ";
					else if (-coef == 1)
						out << " - ";
					else
						out << " + " << coef <<
							" * ";
					if (symbolicnames)
						out << thecell;
					else
						out << (1 + g [d - 1].
							getnumber (thecell));
					cellwritten = true;
				}
			}
			if (cellwritten)
				out << '\n';
		}
		if (!quiet)
		{
			if (d < g. dim ())
				scon << '.';
			else
				scon << ". ";
		}
		out << '\n';
	}
	return out;
} /* writechaincomplex */

/// Creates a relative algebraic chain complex with the data from the given
/// pair of geometric cell complexes.
/// Boundary formulas are restricted to cells which are in the geom. complex.
/// The chain complex should already be initialized with the right dimension.
template <class cell, class euclidom>
chaincomplex<euclidom> &createchaincomplex (chaincomplex<euclidom> &c,
	const gcomplex<cell,euclidom> &g, const gcomplex<cell,euclidom> &rel,
	bool quiet = false)
{
	// if the geometric complex is empty, don't modify the chain complex
	if (g. dim () < 0)
		return c;

	// prepare a table of numbers of ignored cells in the geom. complex
	multitable<int_t> *numbers0 = new multitable<int_t>;
	int_t count0 = g [0]. size ();
	if (rel. dim () >= 0)
	{
		count0 -= rel [0]. size ();
		int_t j = 0;
		for (int_t i = 0; i < rel [0]. size (); ++ i)
		{
			(*numbers0) [j] = g [0]. getnumber (rel [0] [i]);
			if ((*numbers0) [j] < 0)
				++ count0;
			else
				++ j;
		}
	}

	// set the number of generators of the given dimension
	c. def_gen (0, count0);

	// create boundary matrices
	for (int d = 1; d <= g. dim (); ++ d)
	{
		// prepare a table of numbers to be ignored
		multitable<int_t> *numbers1 = new multitable<int_t>;
		int_t count1 = g [d]. size ();
		if (rel. dim () >= d)
		{
			count1 -= rel [d]. size ();
			int_t j = 0;
			for (int_t i = 0; i < rel [d]. size (); ++ i)
			{
				(*numbers1) [j] =
					g [d]. getnumber (rel [d] [i]);
				if ((*numbers1) [j] < 0)
					++ count1;
				else
					++ j;
			}
		}

		// set the number of generators of this dimension
		c. def_gen (d, count1);

		// create the boundary connections with coefficients
		for (int_t i = 0; i < g [d]. size (); ++ i)
		{
			// if this cell is in the other complex, ignore it
			if ((rel. dim () >= d) &&
				(rel [d]. check (g [d] [i])))
				continue;

			// determine the number of this cell
			int_t n1 = i;
			if (n1 >= count1)
				n1 = (*numbers1) [n1 - count1];

			// get the length of the cell
			int len = boundarylength (g [d] [i]);

			// retrieve boundary cells and make boundary formula
			for (int j = 0; j < len; ++ j)
			{
				// take the j-th boundary cell
				cell thecell = boundarycell (g [d] [i], j);

				// add it to the chain complex if relevant
				if (g [d - 1]. check (thecell) &&
					((rel. dim () < d - 1) ||
					(!rel [d - 1]. check (thecell))))
				{
					// determine the number of the cell
					int_t n0 = g [d - 1].
						getnumber (thecell);

					// if out of range, translate it
					if (n0 >= count0)
						n0 = (*numbers0)
							[n0 - count0];

					// determine the right coefficient
					int icoef = boundarycoef
						(g [d] [i], j);
					euclidom coef;
					if (icoef < 0)
					{
						coef = -icoef;
						coef = -coef;
					}
					else
						coef = icoef;

					// add this link to the boundary
					c. add (d, n0, n1, coef);
				}
			}
		}

		// forget unnecessary tables and prepare for the next loop
		delete numbers0;
		numbers0 = numbers1;
		count0 = count1;

		// show progress indicator
		if (!quiet)
		{
			if (d < g. dim ())
				scon << '.';
			else
				scon << ". ";
		}
	}

	// release used memory
	delete numbers0;

	// finish
	return c;
} /* createchaincomplex */

/// Writes the homology generators of the geometric complex to a file.
template <class cell, class euclidom>
std::ostream &writegenerators (std::ostream &out, const chain<euclidom> *hom,
	const chaincomplex<euclidom> &c,
	const gcomplex<cell,euclidom> &g, const int *level = NULL)
{
	bool firstlist = true;
	for (int d = 0; d <= c. dim (); ++ d)
	{
		if ((!level || level [d]) && !hom [d]. empty ())
		{
			if (firstlist)
				firstlist = false;
			else
				out << '\n';
			if (hom [d]. size () == 1)
				out << "The generator of H_" << d <<
					" follows:" << '\n';
			else
				out << "The " << hom [d]. size () <<
					" generators of H_" << d <<
					" follow:" << '\n';
			const hashedset<cell> &cset = g [d];
			for (int_t i = 0; i < hom [d]. size (); ++ i)
			{
				if (hom [d]. size () > 1)
					out << "generator " << (i + 1) <<
						'\n';
				const chain<euclidom> &lst =
					c. gethomgen (d, hom [d]. num (i));
				for (int_t j = 0; j < lst. size (); ++ j)
					out << lst. coef (j) << " * " <<
						cset [lst. num (j)] << '\n';
			}
		}
	}
	return out;
} /* writegenerators */

/// Add a graph of a multivalued cell map to the cell complex.
template <class cell, class euclidom>
gcomplex<cell,euclidom> &creategraph (const mvmap<cell,cell> &m,
	gcomplex<cell,euclidom> &graph)
{
	for (int_t i = 0; i < m. size (); ++ i)
	{
		const cell &e = m. get (i);
		const hashedset<cell> &f = m (i);
		for (int_t j = 0; j < f. size (); ++ j)
			graph. add (e * f [j]);
	}
	return graph;
} /* creategraph */

/// Checks whether this chain complex is acyclic.
/// This verification destroys the chain complex.
/// Acknowledgement: There was a memory leak here - "hom" was not deleted.
/// Thanks to Marc Niethammer for pointing this out. [July 29, 2004]
template <class cell, class euclidom>
bool acyclic (gcomplex<cell,euclidom> &c)
{
	// collapse the geometric complex and check if you can get one elem.
	gcomplex<cell,euclidom> empty;
	c. collapse (empty, empty, true, false, false, NULL, true);
	if (c. size () == 1)
		return true;

	// create the corresponding chain complex and compute its homology
	chaincomplex<euclidom> cx (c. dim ());
	createchaincomplex (cx, c, true);
	chain<euclidom> *hom;
	cx. simple_form (static_cast<int *> (0), true);
	cx. simple_homology (hom, 0);

	// if there is anything above the zero level, the set is not acyclic
	for (int i = 1; i <= cx. dim (); ++ i)
	{
		if (!hom [i]. empty ())
		{
			delete [] hom;
			return false;
		}
	}

	// if there is more than one connected component, it is not acyclic
	if (hom [0]. size () != 1)
	{
		delete [] hom;
		return false;
	}

	// if the coefficient is not 1, the set is not acyclic
	if (hom [0]. getcoefficient (0) == 1)
	{
		delete [] hom;
		return true;
	}
	else
	{
		delete [] hom;
		return false;
	}
} /* acyclic */

// --------------------------------------------------

/// Writes a geometric complex to the output stream in the text format.
template <class cell, class euclidom>
std::ostream &operator << (std::ostream &out,
	const gcomplex<cell,euclidom> &c)
{
	out << "; Geometric complex of dimension " << c. dim () <<
		" (" << c. size () << " cells total)." << '\n';
	for (int i = 0; i <= c. dim (); ++ i)
		out << "; Cells of dimension " << i << ':' << '\n' << c [i];
	return out;
} /* operator << */

/// Reads a geometric complex from an input stream in the text format.
template <class cell, class euclidom>
std::istream &operator >> (std::istream &in, gcomplex<cell,euclidom> &c)
{
	ignorecomments (in);
	while (closingparenthesis (in. peek ()) != EOF)
	{
		cell x;
		in >> x;
		c. add (x);
		ignorecomments (in);
	}
	return in;
} /* operator >> */


// --------------------------------------------------
// ------------------ mv cell map -------------------
// --------------------------------------------------

/// This class represents a multivalued map
/// whose domain is a geometric complex.
template <class cell, class euclidom, class element>
class mvcellmap
{
public:
	/// The constructor of a map with its domain.
	/// The domain of the map must exist during the existence
	/// of the map and its dimension must not increase.
	mvcellmap (gcomplex<cell,euclidom> *_g = 0);

	/// The constructor of a map with its domain.
	/// The domain of the map must exist during the existence
	/// of the map and its dimension must not increase.
	mvcellmap (gcomplex<cell,euclidom> &_g);

	/// The copy constructor.
	mvcellmap (const mvcellmap<cell,euclidom,element> &m);

	/// The assignment operator.
	mvcellmap &operator = (const mvcellmap<cell,euclidom,element> &m);

	/// The destructor.
	~mvcellmap ();

	/// Returns the dimension of the domain of the map.
	int dim () const;

	/// Returns the given level of the geometric complex.
	const hashedset<cell> &get (int d) const;

	/// Returns a reference of the domain cell complex of the map.
	const gcomplex<cell,euclidom> &getdomain () const;

	/// Returns the image of a given cell.
	const hashedset<element> &operator () (const cell &c) const;

	/// Adds a set to the image of a given cell,
	/// provided the dimension of the cell is known.
	void add (int d, const cell &c,
		const hashedset<element> &set);

	/// Adds a set to the image of a given cell.
	void add (const cell &c, const hashedset<element> &set);

	/// Adds a set to the image of a given cell,
	/// provided the dimension and number of the cell is known.
	void add (int d, int_t n, const hashedset<element> &set);

	/// Adds an element to the image of a given cell,
	/// provided the dimension of the cell is known.
	void add (int d, const cell &c, const element &e);

	/// Adds an element to the image of a given cell.
	void add (const cell &c, const element &e);

	/// Adds an element to the image of a given cell,
	/// provided the dimension and number of the cell is known.
	void add (int d, int_t n, const element &e);

private:
	/// A pointer to the domain of the map.
	gcomplex<cell,euclidom> *g;

	/// The array of images of the elements of each dimension.
	multitable <hashedset<element> > *images;

	/// The dimension of the domain of the map.
	int dimension;
	
}; /* class mvcellmap */

// --------------------------------------------------

template <class cell, class euclidom, class element>
inline mvcellmap<cell,euclidom,element>::mvcellmap
	(gcomplex<cell,euclidom> *_g)
{
	g = _g;
	if (!g || (g -> dim () < 0))
	{
		images = NULL;
		dimension = -1;
		return;
	}
	dimension = g -> dim ();
	images = new multitable <hashedset<element> > [dimension + 1];
	if (!images)
		throw "Cannot create a multivalued cellular map.";
	return;
} /* mvcellmap<cell,euclidom,element>::mvcellmap */

template <class cell, class euclidom, class element>
inline mvcellmap<cell,euclidom,element>::mvcellmap
	(gcomplex<cell,euclidom> &_g)
{
	g = &_g;
	if (!g || (g -> dim () < 0))
	{
		images = NULL;
		dimension = -1;
		return;
	}
	dimension = g -> dim ();
	images = new multitable <hashedset<element> > [dimension + 1];
	if (!images)
		throw "Cannot create a multivalued cellular map.";
	return;
} /* mvcellmap<cell,euclidom,element>::mvcellmap */

template <class cell, class euclidom, class element>
mvcellmap<cell,euclidom,element>::mvcellmap
	(const mvcellmap<cell,euclidom,element> &m)
{
	g = m. g;
	if (!g || (g -> dim () < 0))
	{
		images = NULL;
		dimension = -1;
		return;
	}
	dimension = g -> dim ();
	images = new multitable <hashedset<element> > [dimension + 1];
	if (!images)
		throw "Unable to construct a copy of a multivalued "
			"cellular map.";
	for (int i = 0; i < dimension + 1; ++ i)
		images [i] = m. images [i];
	return;
} /* mvcellmap<cell,euclidom,element>::mvcellmap */

template <class cell, class euclidom, class element>
mvcellmap<cell,euclidom,element> &mvcellmap<cell,euclidom,element>::operator =
	(const mvcellmap<cell,euclidom,element> &m)
{
	if (images)
		delete [] images;
	g = m. g;
	dimension = m. dimension;
	if (!g || (dimension < 0))
	{
		images = NULL;
		return *this;
	}
	images = new multitable <hashedset<element> > [dimension + 1];
	if (!images)
		throw "Cannot copy a multivalued cellular map.";
	for (int i = 0; i < dimension + 1; ++ i)
		images [i] = m. images [i];
	return *this;
} /* mvcellmap<cell,euclidom,element>::operator = */

template <class cell, class euclidom, class element>
inline mvcellmap<cell,euclidom,element>::~mvcellmap ()
{
	if (images)
		delete [] images;
	return;
} /* mvcellmap<cell,euclidom,element>::~mvcellmap */

template <class cell, class euclidom, class element>
int mvcellmap<cell,euclidom,element>::dim () const
{
	return dimension;
} /* mvcellmap<cell,euclidom,element>::dim */

template <class cell, class euclidom, class element>
const hashedset<cell> &mvcellmap<cell,euclidom,element>::get (int d) const
{
	if ((d < 0) || (d > dimension))
		throw "Wrong dimension to retrieve from mvcellmap.";
	return (*g) [d];
} /* mvcellmap<cell,euclidom,element>::get */

template <class cell, class euclidom, class element>
const gcomplex<cell,euclidom> &mvcellmap<cell,euclidom,element>::getdomain ()
	const
{
	return *g;
} /* mvcellmap<cell,euclidom,element>::getdomain */

template <class cell, class euclidom, class element>
const hashedset<element> &mvcellmap<cell,euclidom,element>::operator ()
	(const cell &c) const
{
	int d = c. dim ();
	if (d > dimension)
		throw "Trying to get the image of a cell of dim too high.";
	int_t n = (*g) [d]. getnumber (c);
	if (n < 0)
		throw "Trying to get the image of a cell not in the domain.";
	return images [d] [n];
} /* mvcellmap<cell,euclidom,element>::operator () */

template <class cell, class euclidom, class element>
inline void mvcellmap<cell,euclidom,element>::add (int d, const cell &c,
	const hashedset<element> &set)
{
	if ((d < 0) || (d > dimension))
		throw "Wrong dimension for adding a cell to a map.";
	if (!g -> check (c))
	//	throw "The cell does not belong to the domain of the map.";
		g -> add (c);
	images [d] [(*g) [d]. getnumber (c)]. add (set);
	return;
} /* mvcellmap<cell,euclidom,element>::add */

template <class cell, class euclidom, class element>
inline void mvcellmap<cell,euclidom,element>::add (const cell &c,
	const hashedset<element> &set)
{
	add (c. dim (), c, set);
	return;
} /* mvcellmap<cell,euclidom,element>::add */

template <class cell, class euclidom, class element>
inline void mvcellmap<cell,euclidom,element>::add (int d, int_t n,
	const hashedset<element> &set)
{
	if ((d < 0) || (d > dimension))
		throw "Wrong dimension for adding an element to the image.";
	images [d] [n]. add (set);
	return;
} /* mvcellmap<cell,euclidom,element>::add */

template <class cell, class euclidom, class element>
inline void mvcellmap<cell,euclidom,element>::add (int d, const cell &c,
	const element &e)
{
	if ((d < 0) || (d > dimension))
		throw "Wrong dimension for adding a cell to a map.";
	if (!g -> check (c))
	//	throw "The cell does not belong to the domain of the map.";
		g -> add (c);
	images [d] [(*g) [d]. getnumber (c)]. add (e);
	return;
} /* mvcellmap<cell,euclidom,element>::add */

template <class cell, class euclidom, class element>
inline void mvcellmap<cell,euclidom,element>::add (const cell &c,
	const element &e)
{
	add (c. dim (), c, e);
	return;
} /* mvcellmap<cell,euclidom,element>::add */

template <class cell, class euclidom, class element>
inline void mvcellmap<cell,euclidom,element>::add (int d, int_t n,
	const element &set)
{
	if ((d < 0) || (d > dimension))
		throw "Wrong dimension for adding an element to the image.";
	images [d] [n]. add (set);
	return;
} /* mvcellmap<cell,euclidom,element>::add */

// --------------------------------------------------

/// Creates the full graph of a map as a cellular complex.
/// Note: There must be a constructor for 'cell' from 'element'
/// and the Cartesian product operator for cells.
template <class cell, class euclidom, class element>
void creategraph (const mvcellmap<cell,euclidom,element> &m,
	gcomplex<cell,euclidom> &c, bool addbd)
{
	// go through all the dimensions of the domain cell complex
	for (int d1 = 0; d1 <= m. dim (); ++ d1)
	{
		// go through all the cells of this dimension
		const hashedset<cell> &cset = m. get (d1);
		for (int_t i = 0; i < cset. size (); ++ i)
		{
			// create a cell complex of the image of this cell
			const cell &thecell = cset [i];
			const hashedset<element> &set = m (thecell);
			gcomplex<cell,euclidom> img;
			for (int_t j = 0; j < set. size (); ++ j)
				img. add (cell (set [j]));
			if (addbd)
				img. addboundaries ();

			// go through all the dimensions of this cell complex
			for (int d2 = 0; d2 <= img. dim (); ++ d2)
			{
				// add all the products to the graph
				const hashedset<cell> &cs = img [d2];
				for (int_t j = 0; j < cs. size (); ++ j)
					c. add (thecell * cs [j]);
			}
		}
		if (d1 < m. dim ())
			scon << '.';
		else
			scon << ' ';
	}
	return;
} /* creategraph */

/// Creates the full graph of a map as a cellular complex.
/// Note: There must be a constructor for 'cell' from 'element'
/// and the Cartesian product operator for cells.
template <class cell, class euclidom, class element>
void creategraph (const mvcellmap<cell,euclidom,element> &m,
	const gcomplex<cell,euclidom> &rel,
	gcomplex<cell,euclidom> &c, bool addbd)
{
	// go through all the dimensions of the domain cell complex
	for (int d1 = 0; d1 <= m. dim (); ++ d1)
	{
		// go through all the cells of this dimension
		const hashedset<cell> &cset = m. get (d1);
		for (int_t i = 0; i < cset. size (); ++ i)
		{
			// create a cell complex of the image of this cell
			const cell &thecell = cset [i];
			const hashedset<element> &set = m (thecell);
			gcomplex<cell,euclidom> img;
			for (int_t j = 0; j < set. size (); ++ j)
				img. add (cell (set [j]));
			if (addbd)
				img. addboundaries ();

			// go through all the dimensions of this cell complex
			for (int d2 = 0; d2 <= img. dim (); ++ d2)
			{
				// add all the products to the graph
				const hashedset<cell> &cs = img [d2];
				for (int_t j = 0; j < cs. size (); ++ j)
				{
					cell bigcell = thecell * cs [j];
					if (!rel. check (bigcell))
						c. add (bigcell);
				}
			}
		}
		if (d1 < m. dim ())
			scon << '.';
		else
			scon << ' ';
	}
	return;
} /* creategraph */

/// Creates the graph of the map as a cell complex while reducing
/// as possible.
/// Note: There must be a constructor for 'cell' from 'element'
/// and the Cartesian product operator for cells.
template <class cell, class euclidom, class element>
void createcellmap (const mvcellmap<cell,euclidom,element> &m,
	mvcellmap<cell,euclidom,cell> &cm)
{
	// go through all the dimensions of the domain cell complex
	int spacedim = -1;
	const gcomplex<cell,euclidom> &dom = m. getdomain ();
	for (int d = m. dim (); d >= 0; -- d)
	{
		// go through all the cells of this dimension
		const hashedset<cell> &cset = m. get (d);
		for (int_t i = 0; i < cset. size (); ++ i)
		{
			// extract the cell of interest and its image
			const cell &thecell = cset [i];
			const hashedset<element> &set = m (thecell);

			// the image must not be empty!
			if (set. empty ())
				throw "An empty image of a cell found.";

			// correct the dimension of the space if necessary
			if (spacedim < 0)
				spacedim = set [0]. dim ();

			// if this is maximal dimension, extract one point
			if (d == spacedim)
			{
			//	cm. add (d, thecell, cell (set [0]. coord (),
			//		set [0]. coord (), spacedim));
				cm. add (d, thecell, cell (set [0], 0));
				continue;
			}

			// create a cell complex of the image of this cell
			gcomplex<cell,euclidom> img;
			for (int_t j = 0; j < set. size (); ++ j)
				img. add (cell (set [j]));

			// create a cell complex to keep while collapsing
			gcomplex<cell,euclidom> keep;
			const hashedset<cell> &cob =
				dom. getcob (thecell, d);
			for (int_t j = 0; j < cob. size (); ++ j)
				keep. add (cm (cob [j]));

			// reduce 'img' towards 'keep'
			gcomplex<cell,euclidom> empty;
			img. collapse (empty, keep, 1, 0, 0, NULL, 1);

			// set this to be the image of this cell
			// *** THIS MUST BE IMPROVED ***
			for (int j = 0; j <= img. dim (); ++ j)
				cm. add (d, thecell, img [j]);

			// show progress indicator
			if (i && !(i % 373))
				scon << std::setw (12) << i <<
					"\b\b\b\b\b\b\b\b\b\b\b\b";
		}
		if (cset. size () > 373)
			scon << "            \b\b\b\b\b\b\b\b\b\b\b\b";
		scon << '.';
	}
	scon << ' ';
	return;
} /* createcellmap */

/// Creates the graph of the map as a cell complex while reducing
/// as possible.
/// Note: There must be a constructor for 'cell' from 'element'
/// and the Cartesian product operator for cells.
/// The domain of 'rel' must be a subset of the domain of 'm'.
/// If the acyclicity is to be verified, returns true if Ok, false if not.
template <class cell, class euclidom, class element>
bool createcellmap (const mvcellmap<cell,euclidom,element> &m,
	const mvcellmap<cell,euclidom,element> &rel,
	mvcellmap<cell,euclidom,cell> &cm, bool verifyacyclicity)
{
	// prepare the default result
	bool result = true;

	// go through all the dimensions of the domain cell complex
	const gcomplex<cell,euclidom> &dom = m. getdomain ();
	const gcomplex<cell,euclidom> &reldom = rel. getdomain ();

	int maxdim = m. dim ();
	for (int d = maxdim; d >= 0; -- d)
	{
		// go through all the cells of this dimension
		const hashedset<cell> &cset = m. get (d);
		for (int_t i = 0; i < cset. size (); ++ i)
		{
			// extract the cell of interest and its image
			const cell &thecell = cset [i];
			const hashedset<element> &set = m (thecell);

			// the image must not be empty!
			if (set. empty ())
				throw "An empty image of a cell found.";

			// if this is maximal dimension, extract one point
			if (d == maxdim)
			{
				if (reldom. check (thecell))
					continue;
				//	throw "This cell shouldn't be here.";
			//	cm. add (d, thecell, cell (set [0]. coord (),
			//		set [0]. coord (), set [0]. dim ()));
				cm. add (d, thecell, cell (set [0], 0));
				continue;
			}

			// create a cell complex of the image of this cell
			gcomplex<cell,euclidom> img;
			for (int_t j = 0; j < set. size (); ++ j)
				img. add (cell (set [j]));

			// create a cell complex to keep while collapsing
			gcomplex<cell,euclidom> keep;
			const hashedset<cell> &cob =
				dom. getcob (thecell, d);

			for (int_t j = 0; j < cob. size (); ++ j)
				keep. add (cm (cob [j]));

			// create a cell complex from 'rel'
			gcomplex<cell,euclidom> other;
			if (reldom. check (thecell))
			{
				const hashedset<element> &relset =
					rel (thecell);
				for (int_t j = 0; j < relset. size (); ++ j)
				{
					cell c = cell (relset [j]);
					keep. add (c);
					other. add (c);
				//	img. remove (c);
				}
			}

			// reduce 'img' towards 'keep'
			gcomplex<cell,euclidom> empty;
			img. collapse (empty, keep, 1, 0, 0, NULL, 1);

			// verify the acyclicity of this image if requested
			if (verifyacyclicity)
			{
				gcomplex<cell,euclidom> imgdupl (img);
				if (!acyclic (imgdupl))
				{
					result = false;
					verifyacyclicity = false;
				}
			}

			// remove the other cells and their faces from img
			other. addboundaries ();
			img. remove (other);

			// verify the acyclicity of the other complex
			if (verifyacyclicity && other. size ())
			{
				// note: acycl. check destroys 'other'
				if (!acyclic (other))
				{
					result = false;
					verifyacyclicity = false;
				}
			}

			// set this to be the image of this cell
			// *** THIS MUST BE IMPROVED ***
			for (int j = 0; j <= img. dim (); ++ j)
				cm. add (d, thecell, img [j]);

			// show progress indicator
			if (i && !(i % 373))
				scon << std::setw (12) << i <<
					"\b\b\b\b\b\b\b\b\b\b\b\b";
		}
		if (cset. size () > 373)
			scon << "            \b\b\b\b\b\b\b\b\b\b\b\b";
		scon << '.';
	}
	scon << ' ';
	return result;
} /* createcellmap */

// --------------------------------------------------

/// Writes a multivalued cellular map to the output stream.
template <class cell, class euclidom, class element>
std::ostream &operator << (std::ostream &out,
	const mvcellmap<cell,euclidom,element> &m)
{
	for (int d = 0; d <= m. dim (); ++ d)
	{
		out << "; Dimension " << d << ':' << '\n';
		const hashedset<cell> &cset = m. get (d);
		for (int_t i = 0; i < cset. size (); ++ i)
		{
			out << cset [i] << " -> ";
			write (out, m (cset [i]), SMALL_SIZE) << '\n';
		}
	}
	return out;
} /* operator << */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_GCOMPLEX_H_ 

/// @}

