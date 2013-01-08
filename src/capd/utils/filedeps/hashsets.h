/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file hashsets.h
///
/// This file contains the definition of the container "hashedset"
/// which can be used to represent a set of elements of arbitrary type.
/// Hashing tables are used to access the elements in an efficient way.
///
/// Based on the container "hashedset", the container "mvmap" is also
/// defined. It represents a multivalued map which maps each element
/// in its domain to a set of elements contained in its codomain.
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

// Started in January 2002. Last revision: April 23, 2008.


#ifndef _CHOMP_STRUCT_HASHSETS_H_
#define _CHOMP_STRUCT_HASHSETS_H_

#include "config.h"
#include "textfile.h"
#include "integer.h"
#include "multitab.h"

#include <cstdlib>
#include <ctime>
#include <iostream>

namespace chomp {
namespace homology {


// class templates defined within this header file (in this order):
template <class element>
class hashedset;
template <class domelement, class imgelement>
class mvmap;


// --------------------------------------------------
// ------------------- hash stat --------------------
// --------------------------------------------------

/// This is a small class used to gather and display hashing statistics
/// for the hashing tables in the class "hashedset".
class hashstat
{
public:
	/// The constructor.
	hashstat ();

	/// The creation time of the hashed set.
	std::time_t creationtime;

	/// The number of times that an element was found
	/// in the hashing table.
	unsigned long hashhits;

	/// The number of times that an element was not found in the
	/// hashing table, because that entry was used for another element.
	unsigned long hashmisses;

	/// The number of rehashing the table when the size of the hashing
	/// table was changed and all the elements had to be hashed again.
	unsigned long rehashcount;

}; /* class hashstat */

// --------------------------------------------------

inline hashstat::hashstat ()
{
	std::time (&creationtime);
	hashhits = 0;
	hashmisses = 0;
	rehashcount = 0;
	return;
} /* hashstat::hashstat */

// --------------------------------------------------

/// Shows hashing statistics in a concise and readable way
/// to the output stream in the text format.
inline std::ostream &operator << (std::ostream &out, const hashstat &s)
{
	if (!s. hashhits)
		return out;
	out << "hashing: " << s. hashhits << " hits, avg " <<
		((s. hashhits + s. hashmisses) / s. hashhits) << "." <<
		((s. hashhits + s. hashmisses) * 10 / s. hashhits) % 10 <<
		" attempts (" << s. rehashcount << " times rehashed)";
	return out;
} /* operator << */


// --------------------------------------------------
// ------------------- hashed set -------------------
// --------------------------------------------------

/// The default initial size of a hashing table.
#define INITHASHSIZE 137

/// The initial size of a table in a hashed set.
#define INITTABSIZE 30

/// The minimal number of elements above which hashing table is actually
/// used. If the number of elements is below this threshold, then a simple
/// array is used and elements are searched for by going through all the
/// elements of the array.
#define STARTHASHING 30

/// This is a template for a set of objects of the given type.
/// Each of the objects should have two functions for generating hashing
/// keys: "unsigned hashkey1 (const object &x)" and " unsigned hashkey2 (x)".
/// Note: If you remove elements which are not at the end of the set,
/// then the numbers of other elements can change! In the current solution,
/// the last element is put in place of the removed one, but this behavior
/// may be changed in the future versions of this template.
template <class element>
class hashedset
{
public:
	/// The type of elements stored in the set.
	typedef element value_type;

	/// The default constructor for creating an empty set of objects.
	/// If you expect the set to keep a lot of elements,
	/// you may want to set the initial size to something large.
	explicit hashedset (int initialsize = 0, int bequiet = 1);

	/// The copy constructor.
	hashedset (const hashedset<element> &s);

	/// The assignment operator.
	hashedset &operator = (const hashedset<element> &s);

	/// The destructor.
	~hashedset (void);

	/// Finds the given element and returns its number.
	/// Returns -1 if the element is not in the set.
	int getnumber (const element &e) const;

	/// Checks if the given number is an index of some element in the
	/// set, that is, if the number is non-negative and strictly
	/// smaller than the number of elements in the set.
	/// Returns true if yes, false if no.
	bool checknum (int n) const;

	/// Checks if the given element is in the set.
	/// Returns true if yes, false if no.
	bool check (const element &e) const;

	/// Returns the element with the given number from the set.
	const element &operator [] (int n) const;

	/// Returns the element with the given number from the set.
	const element &get (int n) const;

	/// Returns the last element in the set.
	const element &front () const;

	/// Returns the last element in the set.
	const element &top () const;

	/// Adds the given element to the set and returns its number.
	/// If the element was already in the set, it is not added
	/// the second time, only its number is returned.
	int add (const element &e);

	/// Adds the given element to the set and returns its number.
	/// If the element was already in the set, it is not added
	/// the second time, only its number is returned.
	int push (const element &e);

	/// Removes the given element from the set.
	/// Returns 0 if successful, -1 if the element was not in the set.
	int remove (const element &e);

	/// Returns an element with the given number from the set.
	/// Returns 0 if successful, -1 if the number is out of range.
	int removenum (int n);

	/// Removes the last element from the set.
	/// Throws an exception if the set is empty.
	int pop ();

	/// Adds an entire set of elements to the set.
	hashedset<element> &add (const hashedset<element> &s);

	/// Removes an entire set of elements from the set.
	hashedset<element> &remove (const hashedset<element> &s);

	/// Returns the number of elements in the set.
	int size () const;

	/// Returns true if the set is empty. Otherwise returns false.
	bool empty () const;

	/// Swaps two hashed sets by swapping their internal data.
	void swap (hashedset<element> &other);

	/// Computes the intersection of two hashed sets and adds
	/// the result to the current set.
	void intersection (const hashedset<element> &s1,
		const hashedset<element> &s2);

	/// Hashed set statistics. Allocate this structure to make the set
	/// gather usage and effectiveness statistics. By default this
	/// pointer is set to 0. It is deallocated in the destructor.
	hashstat *stat;

private:
	/// The number of elements stored in the set.
	int nelem;

	/// The table of these elements.
	multitable<element> tab;

	/// Is the hashing table in use?
	int hashing;

	/// The size of the hashing table.
	primeint hashsize;

	/// The number of cleared entries in the hashing table.
	int hashcleared;

	/// The hashing table. Each entry contains the index of the element
	/// in the set, or -1 if the entry is free, or -2 if it was cleared.
	multitable<int> hashtable;

	/// Finds the position in the hashing table at which the number
	/// of the given element should be. If there is -1 there, then
	/// the number's element should be written there if adding.
	/// Saves to 'addposition' the first cleared position in the
	/// hashing table if found or sets it to -1 otherwise.
	int hashfind (const element &e, int *addpos = NULL) const;

	/// Replace the old hashing table with a new one.
	/// The desired size may be given, otherwise an optimal size
	/// is determined and the table is made larger or smaller.
	void rehash (int newsize = 0);

}; /* class hashedset */

// --------------------------------------------------

template <class element>
hashedset<element>::hashedset (int initialsize, int bequiet):
	nelem (0), tab ((initialsize > 0) ? initialsize : INITTABSIZE),
	hashing (0),
	hashsize (initialsize + (initialsize >> 2) + INITHASHSIZE),
	hashcleared (0), hashtable (hashsize)
{
	if (bequiet)
		stat = NULL;
	else
		stat = new hashstat;
	return;
} /* hashedset<element>::hashedset */

template <class element>
hashedset<element>::hashedset (const hashedset<element> &s):
	nelem (s. nelem), tab (s. tab),
	hashing (s. hashing), hashsize (s. hashsize),
	hashcleared (s. hashcleared), hashtable (s. hashtable)
{
	if (s. stat)
		stat = new hashstat;
	else
		stat = NULL;
	return;
} /* hashedset<element>::hashedset */

template <class element>
hashedset<element> &hashedset<element>::operator =
	(const hashedset<element> &s)
{
	if (s. stat)
		stat = new hashstat (*stat);

	nelem = s. nelem;
	tab = s. tab;
	hashing = s. hashing;
	hashsize = s. hashsize;
	hashcleared = s. hashcleared;
	hashtable = s. hashtable;

	return *this;
} /* multitable<element>::operator = */

template <class element>
hashedset<element>::~hashedset ()
{
	if (!stat)
		return;
	sout << "  " << *stat << '\n';
	delete stat;
	stat = NULL;
	return;
} /* hashedset<element>::~hashedset */

template <class element>
int hashedset<element>::getnumber (const element &e) const
{
	if (hashing)
	{
		int pos = hashfind (e);
		return (hashtable (pos));
	}
	else
	{
		for (int i = 0; i < nelem; i ++)
			if (tab (i) == e)
				return i;
		return -1;
	}
} /* hashedset<element>::getnumber */

template <class element>
inline bool hashedset<element>::checknum (int n) const
{
	return ((n >= 0) && (n < nelem));
} /* hashedset<element>::checknum */

template <class element>
inline bool hashedset<element>::check (const element &e) const
{
	return (getnumber (e) >= 0);
} /* hashedset<element>::check */


template <class element>
inline const element &hashedset<element>::get (int n) const
{
	if ((n < 0) || (n >= nelem))
		throw "Trying to get an element out of range.";
	return tab (n);
} /* hashedset<element>::get */

template <class element>
inline const element &hashedset<element>::operator [] (int n) const
{
	return get (n);
} /* hashedset<element>::operator [] */

template <class element>
inline const element &hashedset<element>::front () const
{
	return get (nelem - 1);
} /* hashedset<element>::front */

template <class element>
inline const element &hashedset<element>::top () const
{
	return get (nelem - 1);
} /* hashedset<element>::top */

template <class element>
int hashedset<element>::add (const element &e)
{
	if (!hashing)
	{
		for (int i = 0; i < nelem; i ++)
			if (tab (i) == e)
				return i;
		tab [nelem ++] = e;
		if (nelem >= STARTHASHING)
		{
			hashing = 1;
			rehash ();
		}
		return (nelem - 1);
	}

	// rehash if there is very little free space in the hashing table
	if ((int) hashsize - hashcleared < nelem + (nelem >> 1) + 19)
		rehash ();

	// find the position of the element's number in the hashing table
	int addpos = -1;
	int pos = hashfind (e, &addpos);

	// if it alread was in the set, then just return its number
	if (hashtable (pos) >= 0)
		return hashtable (pos);

	// add this element to the set and return its new number
	if (addpos >= 0)
		pos = addpos;
	hashtable [pos] = nelem;
	tab [nelem] = e;
	return nelem ++;
} /* hashedset<element>::add */

template <class element>
inline int hashedset<element>::push (const element &e)
{
	return add (e);
} /* hashedset<element>::push */

template <class element>
int hashedset<element>::remove (const element &e)
{
	if (!hashing)
	{
		for (int i = 0; i < nelem; i ++)
			if (tab (i) == e)
			{
				tab [i] = tab (-- nelem);
				return 0;
			}
		return -1;
	}

	// find the position in the hashing table with this element's number
	int pos = hashfind (e);

	// if it was not there, then finish
	if (hashtable (pos) < 0)
		return -1;
	int n = hashtable (pos);

	// update the hashing table and the number of elements in the set
	hashtable [pos] = -2;
	nelem --;
	hashcleared ++;

	// if it was not the last element in the set, move the last one
	// to the vacated place
	if (n != nelem)
	{
		pos = hashfind (tab (nelem));
		hashtable [pos] = n;
		tab [n] = tab (nelem);
	}

	// if there are very few elements in the table, turn off hashing
	if (nelem < STARTHASHING / 2)
	{
		hashing = 0;
	}

	// if there are very many cleared entries, then rehash
	else if (hashcleared > nelem + 19)
		rehash ();

	return 0;
} /* hashedset<element>::remove */

template <class element>
inline int hashedset<element>::removenum (int n)
{
	if ((n < 0) || (n >= nelem))
		return -1;
	if (!hashing)
	{
		nelem --;
		if (n != nelem)
			tab [n] = tab (nelem);
		return 0;
	}
	return remove (tab (n));
} /* hashedset<element>::removenum */

template <class element>
inline int hashedset<element>::pop ()
{
	if (!nelem)
		throw "Trying to remove an element from an empty set.";
	return removenum (nelem - 1);
} /* hashedset<element>::pop */

template <class element>
hashedset<element> &hashedset<element>::add (const hashedset<element> &s)
{
	int n = s. size ();
	for (int i = 0; i < n; ++ i)
		add (s [i]);
	return *this;
} /* hashedset<element>::add */

template <class element>
hashedset<element> &hashedset<element>::remove (const hashedset<element> &s)
{
	if (this -> size () < s. size ())
	{
		for (int i = 0; i < this -> size (); ++ i)
			if (s. check ((*this) [i]))
				this -> removenum (i --);
	}
	else
	{
		int n = s. size ();
		for (int i = 0; i < n; ++ i)
			remove (s [i]);
	}
	return *this;
} /* hashedset<element>::remove */

template <class element>
inline bool hashedset<element>::empty () const
{
	return !nelem;
} /* hashedset<element>::empty */

template <class element>
inline int hashedset<element>::size () const
{
	return nelem;
} /* hashedset<element>::size */

template <class element>
inline void hashedset<element>::swap (hashedset<element> &other)
{
	my_swap (stat, other. stat);
	my_swap (nelem, other. nelem);
	tab. swap (other. tab);
	my_swap (hashing, other. hashing);
	my_swap (hashsize, other. hashsize);
	my_swap (hashcleared, other. hashcleared);
	hashtable. swap (other. hashtable);
	return;
} /* hashedset<element>::swap */

template <class element>
inline void hashedset<element>::intersection (const hashedset<element> &s1,
	const hashedset<element> &s2)
{
	int size1 = s1. size ();
	int size2 = s2. size ();

	if (size1 <= size2)
	{
		for (int i = 0; i < size1; ++ i)
		{
			const element &elem = s1. tab [i];
			if (s2. check (elem))
				this -> add (elem);
		}
	}
	else
	{
		for (int i = 0; i < size2; ++ i)
		{
			const element &elem = s2. tab [i];
			if (s1. check (elem))
				this -> add (elem);
		}
	}
	return;
} /* hashedset<element>::intersection */

template <class element>
int hashedset<element>::hashfind (const element &e, int *addpos) const
{
	if (!hashing)
		throw "Hashing is turned off.";

	int pos = (int) (hashkey1 (e) % (unsigned) (int) hashsize);
	if (addpos)
		*addpos = -1;

	// start updating hashing statistics
	if (stat)
		stat -> hashhits ++;

	// find the position of the element in the hashing table
	int number, add = 0;
	while ((number = hashtable (pos)) != -1)
	{
		if ((number >= 0) && (e == tab (number)))
			return (pos);
		if (addpos && (*addpos < 0) && (number == -2))
			*addpos = pos;
		if (!add)
			add = (int) (hashkey2 (e) %
				((unsigned) (int) hashsize - 1)) + 1;
		pos += add;
		if (pos >= (int) hashsize)
			pos -= (int) hashsize;
		if (stat)
			stat -> hashmisses ++;
	}

	// return the position located in the hashing table
	return (pos);

} /* hashedset<element>::hashfind */

template <class element>
void hashedset<element>::rehash (int newsize)
{
	if (stat)
		stat -> rehashcount ++;

	// adjust the new size of the hashing table
	if ((newsize < (nelem << 1) + INITHASHSIZE) ||
		(newsize > (nelem << 2) + INITHASHSIZE))
		newsize = (nelem << 1) + nelem + INITHASHSIZE;

	// DEBUG
//	sbug << "(rehash: nelem=" << nelem <<
//		", hashsize=" << hashsize << ", newsize=" << newsize << ")\n";

	// check if it is not too large for 16-bit programs
	int x = 0xFFFF;
	if ((x < 0) && (newsize >= 16384))
		throw "Set too large for a 16-bit program.";

	// free unused memory if desired
	if (newsize < hashsize)
	{
		multitable<int> empty;
		hashtable = empty;
	}
	
	// set the new value of the hashing table and re-buid it
	hashsize = newsize;
	hashcleared = 0;

	// build the entire hash table from the beginning
	hashtable. fill (-1, hashsize);
	for (int i = 0; i < nelem; i ++)
	{
		int pos = hashfind (tab (i));
		if (hashtable (pos) != -1)
			throw "A repeated element in a set!";
		hashtable [pos] = i;
	}

	return;
} /* hashedset<element>::rehash */

// --------------------------------------------------

/// This constant passed to the function 'write' makes the hashed set
/// be displayed in a way that is appropriate for small sets: the entire
/// set is enclosed in braces, and elements are written on one line
/// separated by commas.
#define SMALL_SIZE true

/// This constant passed to the function 'write' makes the hashed set
/// be displayed in a way that is appropriate for large sets: each element
/// is displayed in a separate line, and the elements are preceded by
/// a comment in which the number of elements is indicated and hashing
/// statistics are written.
#define LARGE_SIZE false

/// Writes the entire hashed set to an output stream in the text mode.
/// The operator << is used to write each element of the set.
/// The parameter 'size' should be set either to SMALL_SIZE or LARGE_SIZE.
template <class stream, class element>
stream &write (stream &out, const hashedset<element> &s, bool size)
{
	if (size == SMALL_SIZE)
	{
		out << '{';
		int n = s. size ();
		for (int i = 0; i < n; i ++)
			out << (i ? " " : "") << s [i];
		out << '}';
	}
	else
	{
		int n = s. size ();
		if (!s. empty ())
			out << "; " << n << ((n == 1) ? " element." :
				" elements.") << '\n';
		if (s. stat && s. stat -> hashhits)
			out << ';' << *(s. stat) << '\n';
		for (int i = 0; i < n; ++ i)
			out << s [i] << '\n';
	}
	return out;
} /* write */

/// Writes a hashed set to an output stream as a large one (each element
/// is written on a separate line, with some comments at the beginning).
template <class element>
std::ostream &operator << (std::ostream &out, const hashedset<element> &s)
{
	return write (out, s, LARGE_SIZE);
} /* operator << */

/// Reads a hashed set from an input stream, either a small size style
/// or a large one.
template <class stream, class element>
stream &read (stream &in, hashedset<element> &s, bool size)
{
	// ignore all the comments at the beginning of the input stream
	ignorecomments (in);

	// determine the closing parenthesis
	// and read the opening one if applicable
	int closing = EOF;
	if (size == SMALL_SIZE)
	{
		closing = readparenthesis (in);
		if (closing == EOF)
			throw "An opening parenthesis expected in a set.";
		ignorecomments (in);
	}

	// read the elements until the closing parenthesis is found
	while (in. peek () != closing)
	{
		element e;
		in >> e;
	//	if (!in)
	//		throw "Failed to read an element of a set.";
		s. add (e);
		ignorecomments (in);

		// read a comma between the elements if it is there
		if (in. peek () == ',')
		{
			in. get ();
			ignorecomments (in);
		}
	}

	// read the closing parenthesis if any
	if (closing != EOF)
		in. get ();

	return in;
} /* read */

/// Reads a hashed set from an input stream in a large size style (each
/// element occupies one line, any comments are ignored).
template <class element>
std::istream &operator >> (std::istream &in, hashedset<element> &s)
{
	return read (in, s, LARGE_SIZE);
} /* operator >> */

/// Operator += adds one hashed set to another.
template <class element>
inline hashedset<element> &operator += (hashedset<element> &s,
	const hashedset<element> &u)
{
	s. add (u);
	return s;
} /* operator += */

/// Operator -= removes the contents of one set from another.
template <class element>
inline hashedset<element> &operator -= (hashedset<element> &s,
	const hashedset<element> &u)
{
	s. remove (u);
	return s;
} /* operator -= */

// --------------------------------------------------

/// The first hash key for an unsigned int number.
inline unsigned hashkey1 (unsigned int number)
{
	return number;
} /* hashkey1 */

/// The second hash key for an unsigned int number.
inline unsigned hashkey2 (unsigned int number)
{
	return number & 0x5A5A75A7u;
} /* hashkey2 */

/// This macro is used to define a hash key for any type that can be
/// cast onto an unsigned inteter type, in particular, in the library
/// it is used to define the hash key functions for int, long, and char,
/// both signed and unsigned.
#define DEFHASHKEYS(type) \
inline unsigned hashkey1 (const type &number) \
{ return hashkey1 (static_cast<unsigned> (number)); } \
inline unsigned hashkey2 (const type &number) \
{ return hashkey2 (static_cast<unsigned> (number)); }

DEFHASHKEYS(signed int)
DEFHASHKEYS(unsigned long)
DEFHASHKEYS(signed long)
DEFHASHKEYS(unsigned short)
DEFHASHKEYS(signed short)
DEFHASHKEYS(unsigned char)
DEFHASHKEYS(signed char)

#undef DEFHASHKEYS

/// A template function that extracts the first hash key from an object
/// which has the method "hashkey1".
/// Provided for backwards compatibility with some data types.
template <class T>
inline unsigned hashkey1 (const T &x)
{
	return x. hashkey1 ();
}

/// A template function that extracts the second hash key from an object
/// which has the method "hashkey2".
/// Provided for backwards compatibility with some data types.
template <class T>
inline unsigned hashkey2 (const T &x)
{
	return x. hashkey2 ();
}


// --------------------------------------------------
// ---------------- multivalued map -----------------
// --------------------------------------------------

/// This class defines a multivalued map. Each domain-type element
/// is mapped into a hashed set of image-type elements.
/// The images of elements can be accessed with the operator []
/// (for modifying) and operator () (for retrieval only).
/// NOTE: Since the domain elements can be identified either by their value,
/// or by their successive numbers, the domain cannot be a set of integers,
/// because this would cause ambiguity.
template <class domelement, class imgelement>
class mvmap
{
public:
	/// The default constructor.
	/// The argument 'bequiet' is passed to the hashed set which
	/// represents the domain of the map.
	/// If set to zero, makes the domain display statistics information.
	explicit mvmap (int bequiet = 1);

	/// The destructor.
	~mvmap ();

	/// Retrieves the n-th element from the domain for reading only.
	const domelement &get (int n) const;

	/// Retrieves the domain of the map for reading only.
	const hashedset<domelement> &getdomain () const;

	/// Retrieve the image of the n-th element for reading only.
	/// Throws an exception if the number is out of range.
	const hashedset<imgelement> &operator () (int n) const;

	/// Retrieve the image of an element for reading only.
	/// Throws an exception if the element is not in the domain.
	const hashedset<imgelement> &operator ()
		(const domelement &x) const;

	/// Returns the image of the n-th element for writing.
	hashedset<imgelement> &operator [] (int n);

	/// Returns the image of an element for writing.
	/// If the element is not in the domain, then it is added
	/// and a reference to its empty image is returned.
	hashedset<imgelement> &operator [] (const domelement &x);

	/// Returns the number of elements in the domain of the map.
	int size () const;

//	operator int () const;

	/// Removes an element from the domain of the map.
	/// Returns true if removed, false if it was not in the domain.
	bool remove (const domelement &x);

	/// Removes the n-th element from the domain of the map.
	bool removenum (int n);

	/// Removes a set of elements from the domain of the map.
	void remove (const hashedset<domelement> &x);

	/// Swaps the internal data of two multivalued maps.
	void swap (mvmap<domelement,imgelement> &other);

	/// This variable indicates whether the map should be quiet.
	/// If set to false, the map may display some additional information
	/// about hashing statistics, etc.
	int quiet;

private:
	/// The domain of the map.
	hashedset<domelement> domain;

	/// The images of cubes from the domain. The order of these
	/// images is the same as the order of elements in the domain.
	multitable<hashedset<imgelement> > images;

}; /* class mvmap */

// --------------------------------------------------

template <class domelement, class imgelement>
inline mvmap<domelement,imgelement>::mvmap (int bequiet):
	domain (0, bequiet), images ()
{
	return;
} /* mvmap::mvmap */

template <class domelement, class imgelement>
inline mvmap<domelement,imgelement>::~mvmap ()
{
	return;
} /* mvmap::~mvmap */

template <class domelement, class imgelement>
inline const domelement &mvmap<domelement,imgelement>::get (int n) const
{
	if ((n < 0) || (n >= domain. size ()))
		throw "Domain element number out of range.";
	return domain [n];
} /* mvmap::get */

template <class domelement, class imgelement>
inline const hashedset<domelement> &
	mvmap<domelement,imgelement>::getdomain () const
{
	return domain;
} /* mvmap::getdomain */

template <class domelement, class imgelement>
inline const hashedset<imgelement>
	&mvmap<domelement,imgelement>::operator () (int n) const
{
	if ((n < 0) || (n >= domain. size ()))
		throw "Domain element number out of range.";
	return images (n);
} /* mvmap::operator () */

template <class domelement, class imgelement>
inline const hashedset<imgelement>
	&mvmap<domelement,imgelement>::operator ()
	(const domelement &q) const
{
	int n = domain. getnumber (q);
	if (n < 0)
		throw "Element not in the domain.";
	return images (n);
} /* mvmap::operator () */

template <class domelement, class imgelement>
inline hashedset<imgelement>
	&mvmap<domelement,imgelement>::operator [] (int n)
{
	if ((n < 0) || (n >= domain. size ()))
		throw "Domain element number out of range.";
	return images [n];
} /* mvmap::operator [] */

template <class domelement, class imgelement>
inline hashedset<imgelement>
	&mvmap<domelement,imgelement>::operator []
	(const domelement &q)
{
	int n = domain. add (q);
	return images [n];
} /* mvmap::operator [] */

template <class domelement, class imgelement>
inline int mvmap<domelement,imgelement>::size () const
{
	return domain. size ();
} /* mvmap::size */

/*
template <class domelement, class imgelement>
inline mvmap<domelement,imgelement>::operator int () const
{
	return domain. size ();
}*/ /* mvmap::operator int */

template <class domelement, class imgelement>
inline bool mvmap<domelement,imgelement>::removenum (int n)
// WARNING: This procedure uses the specific way elements are removed from
// a hashed set. If that way is changed, this procedure may not work anymore.
{
	if ((n < 0) || (n >= domain. size ()))
		return false;
	domain. removenum (n);
	images [n] = images [domain. size ()];
	hashedset<imgelement> empty;
	images [domain. size ()] = empty;
	return true;
} /* mvmap::removenum */

template <class domelement, class imgelement>
inline bool mvmap<domelement,imgelement>::remove (const domelement &x)
{
	return removenum (domain. getnumber (x));
} /* mvmap::remove */

template <class domelement, class imgelement>
inline void mvmap<domelement,imgelement>::remove
	(const hashedset<domelement> &x)
{
	int n = x. size ();
	for (int i = 0; i < n; ++ i)
		remove (x [i]);
	return;
} /* mvmap::remove */

template <class domelement, class imgelement>
inline void mvmap<domelement,imgelement>::swap
	(mvmap<domelement,imgelement> &other)
{
	domain. swap (other. domain);
	images. swap (other. images);
	return;
} /* mvmap::swap */

// --------------------------------------------------

/// Adds images of all the elements from the domain of the map to 'img'.
template <class domelement, class imgelement>
hashedset<imgelement> &retrieveimage (const mvmap<domelement,imgelement> &m,
	hashedset<imgelement> &img)
{
	int n = m. getdomain (). size ();
	for (int i = 0; i < n; ++ i)
		img. add (m (i));
	return img;
} /* retrieveimage */

/// Adds a graph of a multivalued map to the given set.
/// The operator * is used to create the Cartesian products (pairs)
/// of elements from the domain and elements in their images.
template <class domelement, class imgelement>
hashedset<imgelement> &creategraph (const mvmap<domelement,imgelement> &m,
	hashedset<imgelement> &graph)
{
	for (int i = 0; i < m. getdomain (). size (); i ++)
	{
		const domelement &e = m. get (i);
		const hashedset<imgelement> &f = m (i);
		int n = f. size ();
		for (int j = 0; j < n; ++ j)
			graph. add (e * f [j]);
	}
	return graph;
} /* creategraph */

// --------------------------------------------------

/// Reads the domain of a multivalued map.
template <class domelement, class imgelement>
std::istream &readdomain (std::istream &in, hashedset<domelement> &dom,
	const mvmap<domelement,imgelement> &)
{
	ignorecomments (in);
	while (in. peek () != EOF)
	{
		domelement e;
		in >> e;
	//	if (!in)
	//		throw "Failed to read a domain element of a map.";
		dom. add (e);

		// read the map's arrow
		ignorecomments (in);
		while (in. peek () == '-')
			in. get ();
		if (in. peek () == '>')
			in. get ();

		ignorecomments (in);
		int closing = readparenthesis (in);

		ignorecomments (in);
		while (in. peek () != closing)
		{
			imgelement junk;
			in >> junk;
		//	if (!in)
		//		throw "Failed to read an image element.";
			ignorecomments (in);
			if (in. peek () == ',')
			{
				in. get ();
				ignorecomments (in);
			}
		}

		if (closing != EOF)
			in. get ();
		ignorecomments (in);
	}
	return in;
} /* readdomain */

/// Reads the image of a multivalued map.
template <class domelement, class imgelement>
std::istream &readimage (std::istream &in, hashedset<imgelement> &img,
	const mvmap<domelement,imgelement> &)
{
	ignorecomments (in);
	while (in. peek () != EOF)
	{
		domelement e;
		in >> e;
	//	if (!in)
	//		throw "Failed to read a domain element of a map.";

		// read the map's arrow
		ignorecomments (in);
		while (in. peek () == '-')
			in. get ();
		if (in. peek () == '>')
			in. get ();

		ignorecomments (in);
		read (in, img, SMALL_SIZE);

		ignorecomments (in);
	}
	return in;
} /* readimage */

/// Reads a restriction of a multivalued map to the union of the given sets.
template <class domelement, class imgelement>
std::istream &readselective (std::istream &in, mvmap<domelement,imgelement> &m,
	const hashedset<domelement> &dom1, const hashedset<domelement> &dom2)
{
	if (dom1. empty () && dom2. empty ())
	{
		sout << "Warning: The domain of the map is empty.\n";
		return in;
	}

	ignorecomments (in);
	while (in. peek () != EOF)
	{
		domelement e;
		in >> e;
	//	if (!in)
	//		throw "Failed to read a domain element of a map.";

		// read the map's arrow
		ignorecomments (in);
		while (in. peek () == '-')
			in. get ();
		if (in. peek () == '>')
			in. get ();

		ignorecomments (in);
		if (dom1. check (e) || dom2. check (e))
			read (in, m [e], SMALL_SIZE);
		else
		{
			int closing = readparenthesis (in);
	
			ignorecomments (in);
			while (in. peek () != closing)
			{
				imgelement junk;
				in >> junk;
			//	if (!in)
			//		throw "Failed to read an img elem.";
				ignorecomments (in);
				if (in. peek () == ',')
				{
					in. get ();
					ignorecomments (in);
				}
			}
	
			if (closing != EOF)
				in. get ();
		}
		ignorecomments (in);
	}
	return in;
} /* readselective */

/// Reads a restriction of a multivalued map to the two given sets.
template <class domelement, class imgelement>
std::istream &readrestriction (std::istream &in,
	mvmap<domelement,imgelement> &m, const hashedset<domelement> &dom,
	const hashedset<imgelement> &img)
{
	if (dom. empty ())
	{
		sout << "Warning: The domain of the map is empty.\n";
		return in;
	}

	ignorecomments (in);
	while (in. peek () != EOF)
	{
		domelement e;
		in >> e;
	//	if (!in)
	//		throw "Failed to read a domain element of a map.";

		// read the map's arrow
		ignorecomments (in);
		while (in. peek () == '-')
			in. get ();
		if (in. peek () == '>')
			in. get ();

		ignorecomments (in);
		if (dom. check (e))
		{
			hashedset<imgelement> &y = m [e];
			hashedset<domelement> x;
			read (in, x, SMALL_SIZE);
			int n = x. size ();
			for (int i = 0; i < n; ++ i)
			{
				if (img. check (x [i]))
					y. add (x [i]);
			}
		}
		else
		{
			int closing = readparenthesis (in);
	
			ignorecomments (in);
			while (in. peek () != closing)
			{
				imgelement junk;
				in >> junk;
			//	if (!in)
			//		throw "Failed to read an img elem.";
				ignorecomments (in);
				if (in. peek () == ',')
				{
					in. get ();
					ignorecomments (in);
				}
			}
	
			if (closing != EOF)
				in. get ();
		}
		ignorecomments (in);
	}
	return in;
} /* readrestriction */

/// Reads a restriction of a multivalued map to the given set.
template <class domelement, class imgelement>
inline std::istream &readselective (std::istream &in,
	mvmap<domelement,imgelement> &m, const hashedset<domelement> &dom)
{
	hashedset<domelement> empty;
	return readselective (in, m, dom, empty);
} /* readselective */


// --------------------------------------------------

/// Writes a multivalued map to the output stream. Each assignment is written
/// in such a way that the element of the domain is followed by the space,
/// the arrow "->", another space, and then the image set is written in the
/// small style (in braces, with commas between the elements).
template <class domelement, class imgelement>
std::ostream &operator << (std::ostream &out,
	const mvmap<domelement,imgelement> &m)
{
	int n = m. getdomain (). size ();
	for (int i = 0; i < n; ++ i)
	{
		out << m. get (i) << " -> ";
		write (out, m (i), SMALL_SIZE) << '\n';
	}
	return out;
} /* operator << */

/// Reads a multivalued map from an input stream.
template <class domelement, class imgelement>
std::istream &operator >> (std::istream &in, mvmap<domelement,imgelement> &m)
{
	ignorecomments (in);
	while (in. peek () != EOF)
	{
		domelement e;
		in >> e;
	//	if (!in)
	//		throw "Failed to read a domain element of a map.";

		// read the map's arrow
		ignorecomments (in);
		while (in. peek () == '-')
			in. get ();
		if (in. peek () == '>')
			in. get ();

		ignorecomments (in);
		read (in, m [e], SMALL_SIZE);

		ignorecomments (in);
	}
	return in;
} /* operator >> */


} // namespace homology
} // namespace chomp

#endif // _CHOMP_STRUCT_HASHSETS_H_

/// @}

