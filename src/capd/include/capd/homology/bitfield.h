/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bitfield.h
///
/// This file contains the definition of a bitfield class which works
/// an array of bits. The functionality of this class is very limited
/// and it is optimized for the specific application in the homology
/// computation algorithms.
///
/// Note that memory allocation and deallocation,
/// as well as remembering the length of the bitfield is the responsibility
/// of the code which uses the bitfield, the class bitfield doesn't take
/// care of these issues.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in April 1999. Last revision: May 24, 2010.


#ifndef _CAPD_HOMOLOGY_BITFIELD_H_ 
#define _CAPD_HOMOLOGY_BITFIELD_H_ 

#include "capd/homology/config.h"

#include <iostream>
#include <cstdlib>

namespace capd {
namespace homology {


// classes defined within this header file:
class BitField;
class SetOfBitFields;

/// A lower-case version of the name of a bit field [deprecated].
typedef BitField bitfield;

/// A lower-case version of the name of a bit field set [deprecated].
typedef SetOfBitFields bitfieldset;


// --------------------------------------------------
// ------------------- BitField ---------------------
// --------------------------------------------------

/// This class defines a bit field that is part of some larger array
/// or that uses an allocated piece of memory. This class may be useful
/// for efficient management of multiple bit fields, or just one bit field.
/// Note the very specific behavior of memory management!
class BitField
{
public:
	/// The constructor of an undefined bit field.
	BitField ();

	/// The destructor which actually does nothing.
	~BitField ();

	/// Returns true if the bit field has already been defined,
	/// that is, it is bound with some memory piece, or its memory
	/// has been allocated.
	bool defined () const;

	/// Define the bit field as a piece of a larger memory buffer.
	/// The memory enough to store the given number of bits
	/// (the length of the bit field) will be used.
	void define (unsigned char *buf, int_t length);

	/// Allocates memory for a bit field.
	/// The memory enough to store the given number of bits (the length
	/// of the bit field) is allocated with the 'new' operator.
	void allocate (int_t length);

	/// Releases the memory allocated for the bit field.
	/// This must be used if the memory was allocated, because
	/// the destructor does not deallocte the memory.
	void free ();

	/// Sets the given bit to 1.
	void set (int_t n);

	/// Clears the given bit (sets it to 0).
	void clear (int_t n);

	/// Tests the given bit. Returns 0 or 1.
	int test (int_t n) const;

	/// Copies all the bits from the given bitfield.
	/// Assumes that both bit fields have the specified length.
	/// Note that the bit field itself does not store its length.
	void takebits (const BitField &from, int_t length);

	/// Clears all the bits in the entire bit field of specified length.
	/// Note that the bit field itself does not store its length.
	void clearall (int_t length);

	/// Finds the first bit that is set to 1, beginning at the given one.
	/// Return the number of the bit, or -1 if not found.
	/// Note that the bit field itself does not store its length,
	/// so this length must be provided as an argument of this function.
	int find (int_t after, int_t length) const;

	/// Returns the first key for hashing.
	/// Note that the bit field itself does not store its length,
	/// so this length must be provided as an argument of this function.
	int_t hashkey (int_t length) const;

	/// Returns the second key for hashing.
	/// Note that the bit field itself does not store its length,
	/// so this length must be provided as an argument of this function.
	int_t hashadd (int_t length) const;

	/// Compares two bit fields of the giben length.
	/// Returns true if they are the same, false otherwise.
	friend bool thesame (const BitField &b1, const BitField &b2,
		int_t length);

	/// Converts an integer into the bits of a bit field of the given
	/// length. The length must not exceed the size of the integer.
	friend void int2bits (int bits, int_t length, BitField &field);

	/// Converts the bits of a bit field of the given length into
	/// an integer. The length must not exceed the size of the integer.
	friend int bits2int (const BitField &field, int_t length);

private:
	/// The table of 8-bit cells which store the subsequent bits.
	/// It is either an address of some allocated memory, or an address
	/// of portion of some other memory, for example, allocated
	/// collectively for a large number of bit fields.
	unsigned char *table;

}; /* BitField */

// --------------------------------------------------

inline BitField::BitField ()
{
	table = NULL;
	return;
} /* BitField::BitField */

inline bool BitField::defined () const
{
	return !!table;
} /* BitField::defined */

inline void BitField::free ()
{
	delete [] table;
	table = NULL;
	return;
} /* BitField::free */

inline BitField::~BitField ()
{
	return;
} /* BitField::~BitField */

inline void BitField::set (int_t n)
{
	table [n >> 3] |= static_cast<unsigned char> (0x01 << (n & 0x07));
	return;
} /* BitField::set */

inline void BitField::clear (int_t n)
{
	table [n >> 3] &= static_cast<unsigned char> (~(0x01 << (n & 0x07)));
	return;
} /* BitField::clear */

inline int BitField::test (int_t n) const
{
	return !!(table [n >> 3] & (0x01 << (n & 0x07)));
} /* BitField::test */

inline void int2bits (int bits, int_t length, BitField &field)
{
	unsigned char *tab = field. table;
	if (!tab)
		throw "Trying to set values to an undefined bitfield.";
	while (length >= 0)
	{
		*(tab ++) = static_cast<unsigned char> (bits & 0xFF);
		bits >>= 8;
		length -= 8;
	}
	return;
} /* int2bits */

inline int bits2int (const BitField &field, int_t length)
{
	const unsigned char *tab = field. table;
	if (!tab)
		throw "Trying to set values to an undefined bitfield.";
	int n = 0;
	int shiftvalue = 0;
	while (length >= 8)
	{
		n |= (*(tab ++)) << shiftvalue;
		length -= 8;
		shiftvalue += 8;
	}
	const int bitmasks [] = {0x00, 0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3F, 0x7F, 0xFF};
	if (length > 0)
		n |= ((*(tab ++)) & bitmasks [length]) << shiftvalue;
	return n;
} /* bits2int */


// --------------------------------------------------
// ----------------- SetOfBitFields -----------------
// --------------------------------------------------

/// This class defines a set of bit fields of the same length
/// which are to be stored in a contiguous piece of memory
/// to avoid multiple memory allocation/deallocation.
/// Each bit field in the set is assigned a value 1 or 0.
/// Hashing is used for quick retrieval of the values of bit fields.
class SetOfBitFields
{
public:
	/// The constructor of a set of a fixed maximal number of bit fields,
	/// each of the same length. The set is initially empty.
	SetOfBitFields (int_t len, int_t maxelem);

	/// The destructor.
	~SetOfBitFields ();

	/// Adds a bit field to the set. If it already was there then returns
	/// its value. If there is no room available for the bit field
	/// then returns -1. Otherwise returns 2.
	int add (const BitField &b, int value);

	/// Returns the value of the given bit field value
	/// or return -1 if the bit field is not in the set.
	int check (const BitField &b) const;

	/// Returns the number of bit fields contained in the set.
	int used (void) const;

	/// Forgets all the bit fields and deallocates the memory.
	void forget ();

private:
	/// The number of bit fields that still can be stored.
	int avail;

	/// The number of bit fields used.
	int usedcount;

	/// The actual size of the table.
	int_t size;

	/// The length of bit fields.
	int_t length;

	/// The table of bit fields.
	BitField *bf;

	/// The values of bit fields.
	BitField values;

	/// The memory buffer used for bit fields.
	unsigned char *buf;

	/// The current position in the buffer.
	unsigned char *bufcur;

}; /* class SetOfBitFields */

// --------------------------------------------------

inline SetOfBitFields::~SetOfBitFields ()
{
	if (bf)
		delete [] bf;
	if (buf)
		delete [] buf;
	if (length)
		values. free ();
	return;
} /* SetOfBitFields::~SetOfBitFields */

inline int SetOfBitFields::used () const
{
	return usedcount;
} /* SetOfBitFields::used */

inline void SetOfBitFields::forget ()
{
	if (bf)
		delete [] bf;
	bf = NULL;
	if (buf)
		delete [] buf;
	buf = NULL;
	if (length)
		values. free ();
	length = 0;
	size = 0;
	avail = 0;
	return;
} /* SetOfBitFields::forget */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_BITFIELD_H_ 

/// @}

