/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file multitab.h
///
/// This file contains the definition of the container "multitable"
/// which is essentially an automatically extendable array whose memory
/// is allocated in small chunks which hold the elements.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2008 by Pawel Pilarczyk.
//
// This file is part of the Homology Library.  This library is free software;
// you can redistribute it and/or modify it under the terms of the GNU
// General Public License as published by the Free Software Foundation;
// either version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this software; see the file "license.txt".  If not, write to the
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

// Started in January 2002. Last revision: February 21, 2007.


#ifndef _CHOMP_STRUCT_MULTITAB_H_
#define _CHOMP_STRUCT_MULTITAB_H_

#include "config.h"
//#include "textfile.h"
//#include "integer.h"

//#include <cstdlib>
//#include <ctime>
//#include <iostream>

namespace chomp {
namespace homology {


// --------------------------------------------------
// ------------------- swap data --------------------
// --------------------------------------------------

template <typename T>
inline void my_swap (T &x, T &y)
{
	T tmp = x;
	x = y;
	y = tmp;
	return;
} /* my_swap */


// --------------------------------------------------
// ------------------ multi table -------------------
// --------------------------------------------------

/// The default size of a piece used in the multi-table.
#define DEFAULTPIECESIZE 32

/// A container for elements placed in a table (like a vector)
/// that is actually built of many smaller tables. This may be important
/// for good memory allocation.
/// The table extends automatically upon use of elements that are outside
/// the range of its indices.
template <class element>
class multitable
{
public:
	/// The default constructor for a table with the given size
	/// of each piece (should be a power of 2 or is rounded up).
	multitable (int piecesize = 0);

	/// The copy constructor.
	multitable (const multitable<element> &m);

	/// The assignment operator.
	multitable<element> &operator = (const multitable<element> &m);

	/// The destructor.
	~multitable ();

	/// Returns a reference of an element for reading/writing.
	/// If the index is out of range, the table is automatically
	/// extended.
	element &operator [] (int n);

	/// Returns a reference of an element for reading only.
	/// Throws an error message if the index is out of range.
	const element &operator () (int n) const;

	/// Returns a reference of an element for reading only.
	/// Throws an error message if the index is out of range.
	const element &operator [] (int n) const;

	/// Allocates the table for holding 'n' elements.
	/// The table is still able to grow further if necessary.
	void allocate (int n);

	/// Fills the table from 0 to the given index
	/// with the given element.
	void fill (const element &e, int n);

	/// Swaps data with another multitable object.
	void swap (multitable<element> &other);

private:
	/// The number of pieces ready to allocate.
	int npieces;

	/// The number of bits to shift the index of an element
	/// in the table.
	int shiftbits;

	/// The mask to get the offset of an element in a table piece.
	int offsetmask;

	/// The actual tables.
	element **tab;

	/// Increases the number of pieces to the desired one.
	void increase (int n);

}; /* class multitable */

// --------------------------------------------------

template <class element>
inline multitable<element>::multitable (int piecesize)
{
	tab = 0;
	npieces = 0;
	if (piecesize <= 0)
		piecesize = DEFAULTPIECESIZE;
	shiftbits = 1;
	while ((1 << shiftbits) < piecesize)
		++ shiftbits;
	offsetmask = (1 << shiftbits) - 1;
	return;
} /* multitable<element>::multitable */

template <class element>
multitable<element>::multitable (const multitable<element> &m):
	npieces (m. npieces), shiftbits (m. shiftbits),
	offsetmask (m. offsetmask)
{
	int piecesize = 1 << shiftbits;
	tab = new element * [npieces];
	if (!tab)
		throw "Cannot alloc mem in copying constructor of a table.";
	for (int i = 0; i < npieces; ++ i)
		if (m. tab [i])
		{
			tab [i] = new element [piecesize];
			if (!tab [i])
				throw "No memory in copying constr.";
			for (int j = 0; j < piecesize; ++ j)
				tab [i] [j] = m. tab [i] [j];
		}
		else
			tab [i] = 0;
	return;
} /* multitable<element>::multitable */

template <class element>
multitable<element> &multitable<element>::operator =
	(const multitable<element> &m)
{
	// have all the tables been deallocated?
	int deallocated = 0;

	// if the size of pieces does not match, they must be deallocated
	if (shiftbits != m. shiftbits)
	{
		// deallocate all the pieces
		for (int i = 0; i < npieces; ++ i)
			if (tab [i])
			{
				delete [] tab [i];
				tab [i] = 0;
			}

		deallocated = 1;
		shiftbits = m. shiftbits;
		offsetmask = m. offsetmask;
	}

	// if the number of pieces is not the same, change the table
	// and for the moment gather in the new table all the pieces
	// that are already allocated
	if (npieces != m. npieces)
	{
		// allocate a new table of pieces
		element **newtab = (m. npieces) ?
			(new element * [m. npieces]) : 0;
		if (!newtab && m. npieces)
			throw "No memory for a table in operator =.";

		// if there may be some not deallocated elements,
		// gather them at the beginning of the table
		// and set the rest of the pointers to 0s
		if (!deallocated)
		{
			// 'i' points to the current entry in the new table,
			// 'j' points to the current entry in the old table
			int i = 0, j = 0;
			while (i < m. npieces)
			{
				// find an allocated piece in the old table
				while ((j < npieces) && !tab [j])
					j ++;
				// if found, take it to the new table
				if (j < npieces)
					newtab [i ++] = tab [j ++];
				// otherwise zero the rest of the new table
				else
					while (i < m. npieces)
						newtab [i ++] = 0;
			}
			// if there are some pieces remaining, delete them
			while (j < npieces)
			{
				if (tab [j])
					delete [] tab [j];
				j ++;
			}
		}
		else
		{
			for (int i = 0; i < m. npieces; i ++)
				newtab [i] = 0;
		}

		if (tab)
			delete [] tab;
		tab = newtab;
		npieces = m. npieces;
	}

	// if the table is empty, then finish now
	if (!npieces)
		return *this;

	// copy the data from 'm' to the current table;
	// try to use pieces which are already allocated
	int first_nonempty = 0, first_empty = 0, pos = 0;
	int piecesize = 1 << shiftbits;

	// find the first nonempty piece and the first empty one
	while ((first_nonempty < npieces) && !tab [first_nonempty])
		first_nonempty ++;
	while ((first_empty < npieces) && tab [first_empty])
		first_empty ++;

	// copy all the pieces
	while (pos < npieces)
	{
		if (m. tab [pos])
		{
			if (!tab [pos])
			{
				if (first_nonempty < npieces)
				{
					tab [pos] = tab [first_nonempty];
					tab [first_nonempty ++] = 0;
				}
				else
				{
					tab [pos] = new element [piecesize];
					if (!tab [pos])
						throw "Error in operator =.";
				}
				first_empty ++;
			}
			else
				first_nonempty ++;

			// copy the source piece to this piece
			for (int i = 0; i < (1 << shiftbits); i ++)
				tab [pos] [i] = m. tab [pos] [i];
		}
		else if (tab [pos])
		{
			if (first_empty < npieces)
			{
				tab [first_empty] = tab [pos];
				first_empty ++;
			}
			else
				delete [] tab [pos];
			first_nonempty ++;
			tab [pos] = 0;
		}
		else
			first_empty ++;

		// move to the next position
		pos ++;

		// update pointers to the first available [non]empty piece
		while ((first_nonempty < npieces) && !tab [first_nonempty])
			first_nonempty ++;
		while ((first_empty < npieces) && tab [first_empty])
			first_empty ++;
	}

	return *this;
} /* multitable<element>::operator = */

template <class element>
inline multitable<element>::~multitable ()
{
	if (!tab)
		return;
	for (int i = 0; i < npieces; i ++)
		if (tab [i])
			delete [] tab [i];
	delete [] tab;
	return;
} /* multitable<element>::~multitable */

template <class element>
inline element &multitable<element>::operator [] (int n)
{
	if (n < 0)
		throw "Negative index of an element in a table used.";

	// calculate the number of piece of interest
	int piece = n >> shiftbits;

	// increase the number of pieces if necessary
	if (piece >= npieces)
	{
		int newnpieces = 2 * npieces + 1;
		if (newnpieces <= piece)
			newnpieces = piece + 1;
		increase (newnpieces);
	}

	// allocate the piece if necessary
	if (!tab [piece])
	{
		tab [piece] = new element [1 << shiftbits];
		if (!tab [piece])
			throw "Cannot allocate a piece of a table";
	}

	return tab [piece] [n & offsetmask];
} /* multitable<element>::operator [] */

template <class element>
inline const element &multitable<element>::operator () (int n) const
{
	if (n < 0)
		throw "Negative index of an element in a table used.";

	// calculate the number of piece of interest
	int piece = n >> shiftbits;

	if ((piece >= npieces) || (!tab [piece]))
		throw "Non-existent table entry requested.";

	return tab [piece] [n & offsetmask];
} /* multitable<element>::operator () */

template <class element>
inline const element &multitable<element>::operator [] (int n) const
{
	return (*this) (n);
} /* multitable<element>::operator [] const */

template <class element>
void multitable<element>::allocate (int n)
{
	if (n <= 0)
		return;
	int piecesize = 1 << shiftbits;
	int necessarypieces = (n + piecesize - 1) / piecesize;

	// allocate more pieces if needed
	if (necessarypieces > npieces)
		increase (necessarypieces);

	// deallocate unnecessary pieces
	for (int i = necessarypieces; i < npieces; i ++)
		if (tab [i])
		{
			delete [] tab [i];
			tab [i] = 0;
		}
	return;
} /* multitable<element>::allocate */

template <class element>
void multitable<element>::fill (const element &e, int n)
{
	if (n <= 0)
		return;
	int piecesize = 1 << shiftbits;
	int maxpiece = (n + piecesize - 1) / piecesize;
	if (maxpiece > npieces)
		increase (maxpiece);
	for (int piece = 0; piece < maxpiece; piece ++)
	{
		if (!tab [piece])
		{
			tab [piece] = new element [piecesize];
			if (!tab [piece])
				throw "Too little mem for a piece.";

		}
		if ((piece == maxpiece - 1) && (n & offsetmask))
			piecesize = n & offsetmask;
		for (int i = 0; i < piecesize; i ++)
			tab [piece] [i] = e;
	}
	return;
} /* multitable<element>::fill */

template <class element>
inline void multitable<element>::swap (multitable<element> &other)
{
	my_swap (npieces, other. npieces);
	my_swap (shiftbits, other. shiftbits);
	my_swap (offsetmask, other. offsetmask);
	my_swap (tab, other. tab);
	return;
} /* multitable<element>::swap */

template <class element>
void multitable<element>::increase (int n)
{
	// DEBUG
//	if (n != 1)
//		sbug << "Inc " << n << ".\n";
	if (n <= npieces)
		throw "Trying to increase a multitable incorrectly.";
	element **newtab = new element * [n];
	if (!newtab)
		throw "Cannot increase a table.";
	int i;
	for (i = 0; i < npieces; i ++)
		newtab [i] = tab [i];
	for (i = npieces; i < n; i ++)
		newtab [i] = 0;
	delete [] tab;
	tab = newtab;
	npieces = n;
	return;
} /* multitable<element>::increase */


} // namespace homology
} // namespace chomp

#endif // _CHOMP_STRUCT_MULTITAB_H_

/// @}

