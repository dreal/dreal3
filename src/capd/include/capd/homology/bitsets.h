/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bitsets.h
///
/// This file defines a class that uses bit representation of a set
/// to store many small sets.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on February 22, 2007. Last revision: June 11, 2010.


#ifndef _CAPD_HOMOLOGY_BITSETS_H_ 
#define _CAPD_HOMOLOGY_BITSETS_H_ 

#include "capd/homology/config.h"

#include <iostream>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------------- BitSets ---------------------
// --------------------------------------------------

/// This class uses bit representation to store many small sets.
/// Each of the sets can contain integer numbers from 0 to the limit
/// specified in the constructor. The number of sets must also be given
/// in the constructor. A contiguous chunk of memory is used to store
/// the bits that represent the sets.
/// This class is not fool-proof, so use it carefully.
/// Minimal interface, sorry.
class BitSets
{
public:
	/// Constructor of a family of empty sets.
	/// The number of the sets and the maximal number of elements
	/// in each set must be provided at initialization.
	BitSets (int_t _nsets, int_t _nelem);

	/// Copy constructor.
	BitSets (const BitSets &s);

	/// Assignment operator.
	BitSets &operator = (const BitSets &s);

	/// Destructor.
	~BitSets ();

	/// Adds an element to the given set.
	void add (int_t n, int_t e);

	/// Removes an element from the given set.
	void remove (int_t n, int_t e);

	/// Checks if an element belongs to the given set.
	bool check (int_t n, int_t e) const;

	/// Adds the entire set 'm' to the set 'n'.
	void addset (int_t n, int_t m);

	/// Retrieves an element >= 'start' in the given set.
	/// Returns -1 if none.
	int_t get (int_t n, int_t start = 0) const;

private:
	/// The number of sets.
	int_t nsets;
	
	/// The maximal number of elements in each set.
	int_t nelem;

	/// The number of bytes used for each set.
	int_t nbytes;

	/// The memory buffer for storing the bits.
	unsigned char *bits;

}; /* BitSets */

// --------------------------------------------------

inline BitSets::BitSets (int_t _nsets, int_t _nelem):
	nsets (_nsets), nelem (_nelem), nbytes ((_nelem + 7) >> 3), bits (0)
{
	int_t size = nsets * nbytes;
	bits = new unsigned char [size];
	for (int_t i = 0; i < size; ++ i)
		bits [i] = 0;
	return;
} /* BitSets::BitSets */

inline BitSets::BitSets (const BitSets &s):
	nsets (s. nsets), nelem (s. nelem), nbytes (s. nbytes), bits (0)
{
	int_t size = nsets * nbytes;
	bits = new unsigned char [size];
	for (int_t i = 0; i < size; ++ i)
		bits [i] = s. bits [i];
	return;
} /* BitSets::BitSets */

inline BitSets &BitSets::operator = (const BitSets &s)
{
	delete [] bits;
	nsets = s. nsets;
	nelem = s. nelem;
	nbytes = s. nbytes;
	int_t size = nsets * nbytes;
	bits = new unsigned char [size];
	for (int_t i = 0; i < size; ++ i)
		bits [i] = s. bits [i];
	return *this;
} /* BitSets::operator = */

inline BitSets::~BitSets ()
{
	delete [] bits;
	return;
} /* BitSets::~BitSets */

inline void BitSets::add (int_t n, int_t e)
{
//	sbug << "Add " << e << " to " << n << ".\n";
	unsigned char *buf = bits + n * nbytes;
	buf [e >> 3] |= (unsigned char) (0x01 << (e & 0x07));
	return;
} /* BitSets::add */

inline void BitSets::remove (int_t n, int_t e)
{
	unsigned char *buf = bits + n * nbytes;
	buf [e >> 3] &= (unsigned char) ~(0x01 << (e & 0x07));
	return;
} /* BitSets::remove */

inline bool BitSets::check (int_t n, int_t e) const
{
	unsigned char *buf = bits + n * nbytes;
	return !!(buf [e >> 3] & (0x01 << (e & 0x07)));
} /* BitSets::check */

inline void BitSets::addset (int_t n, int_t m)
{
	unsigned char *nbuf = bits + n * nbytes;
	unsigned char *mbuf = bits + m * nbytes;
	for (int_t i = 0; i < nbytes; ++ i)
		*(nbuf ++) |= *(mbuf ++);
	return;
} /* BitSets::addset */

inline int_t BitSets::get (int_t n, int_t start) const
{
	if (start >= nelem)
		return -1;
	unsigned char *buf = bits + n * nbytes;
	int_t offset = start >> 3;
	int bit = start & 0x07;
	if (buf [offset] & (0xFF << bit))
	{
		for (; bit < 8; ++ bit)
		{
			if (buf [offset] & (0x01 << bit))
				return (offset << 3) + bit;
		}
		throw "Wrong bit number in BitSets.";
	}
	for (++ offset; offset < nbytes; ++ offset)
	{
		if (!buf [offset])
			continue;
		for (int bit = 0; bit < 8; ++ bit)
		{
			if (buf [offset] & (0x01 << bit))
				return (offset << 3) + bit;
		}
		throw "False bit in BitSets.";
	}
	return -1;
} /* BitSets::get */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_BITSETS_H_ 

/// @}

