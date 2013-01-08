/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bitfield.cpp
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


#include "capd/homology/config.h"
#include "capd/homology/bitfield.h"

#include <iostream>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------------- BITFIELD ---------------------
// --------------------------------------------------

void BitField::define (unsigned char *buf, int_t length)
{
	table = buf;
	register int_t len = (length + 7) >> 3;
	for (int_t i = 0; i < len; i ++)
		table [i] = 0;
	return;
} /* BitField::define */

void BitField::allocate (int_t length)
{
	register int_t len = (length + 7) >> 3;
	table = new unsigned char [len];
	if (!table)
		throw "Not enough memory for a bit field.";
	for (int_t i = 0; i < len; i ++)
		table [i] = 0;
	return;
} /* BitField::allocate */

void BitField::takebits (const BitField &from, int_t length)
{
	register int_t len = (length + 7) >> 3;
	for (int_t i = 0; i < len; i ++)
		table [i] = from. table [i];
	return;
} /* BitField::takebits */

void BitField::clearall (int_t length)
{
	register int_t len = (length + 7) >> 3;
	for (int_t i = 0; i < len; i ++)
		table [i] = 0;
	return;
} /* BitField::clearall */

bool thesame (const BitField &b1, const BitField &b2, int_t length)
{
	register int_t len = (length + 7) >> 3;
	for (int_t i = 0; i < len; i ++)
	{
		if (b1. table [i] != b2. table [i])
			return 0;
	}
	return 1;
} /* thesame */

int_t BitField::hashkey (int_t length) const
{
	int shift = 0;
	int_t key = 0;
	int maxshift = (sizeof (int_t) << 3) - 5;
	int_t len = (length + 7) >> 3;
	for (int_t i = 0; i < len; i ++)
	{
		key ^= static_cast<int_t> (table [i]) << shift;
		shift += 7;
		if (shift > maxshift)
			shift -= maxshift;
	}
	if (key < 0)
		return -(key + 1);
	return key;
} /* BitField::hashkey */

int_t BitField::hashadd (int_t length) const
{
	int shift = 3;
	int_t key = 0x0F0F;
	int maxshift = (sizeof (int_t) << 3) - 5;
	int_t len = (length + 7) >> 3;
	for (int_t i = 0; i < len; i ++)
	{
		key ^= static_cast<int_t> (table [i]) << shift;
		shift += 5;
		if (shift > maxshift)
			shift -= maxshift;
	}
	if (key < 0)
		return -(key + 1);
	return key;
} /* BitField::hashadd */

int BitField::find (int_t first, int_t length) const
{
	// reset the number of the first bit if negative
	if (first < 0)
		first = 0;

	// if the answer is trivial, return it
	if (first >= length)
		return -1;

	// masks for bits with numbers greater than or equal to the given one
	const unsigned char uppermask [] =
		{0xFF, 0xFE, 0xFC, 0xF8, 0xF0, 0xE0, 0xC0, 0x80};
	// masks for bits to consider in the last analyzed byte
	const unsigned char lowermask [] =
		{0xFF, 0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3F, 0x7F};
	// masks for single bits with the given numbers
	const unsigned char bitmask [] =
		{0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80};

	// prepare the numbers of bit masks in the first analyzed byte
	// and in the last analyzed byte
	unsigned char firstmask = uppermask [first & 0x07];
	unsigned char lastmask = lowermask [length & 0x07];

	// figure out the first and last bytes' addresses
	const unsigned char *curbyte = table + (first >> 3);
	const unsigned char *lastbyte = table + ((length - 1) >> 3);

	// if the first byte is the last byte, return the answer
	if (curbyte == lastbyte)
	{
		if (!((*curbyte) & firstmask & lastmask))
			return -1;
	}
	// if there is something in the first byte, return it
	if ((*curbyte) & firstmask)
	{
		int curbit = static_cast<int> (first & 0x07);
		while (curbit < 8)
			if ((*curbyte) & bitmask [curbit])
				return ((curbyte - table) << 3) + curbit;
			else
				curbit ++;
		throw "Bit not found.";
	}
	// otherwise move to the next byte
	else
		++ curbyte;

	// scan all the bytes but the last one in search for a nonzero bit
	while ((curbyte < lastbyte) && !*curbyte)
		++ curbyte;

	// if found, extract the bit
	if ((curbyte < lastbyte) || (*(lastbyte) & lastmask))
	{
		int curbit = 0;
		while (curbit < 8)
			if ((*curbyte) & bitmask [curbit])
				return ((curbyte - table) << 3) + curbit;
			else
				++ curbit;
		throw "Could not find the bit.";
	}

	return -1;
} /* BitField::find */


// --------------------------------------------------
// ----------------- BITFIELDSET --------------------
// --------------------------------------------------

static int_t isprime (int_t n)
// Checks if the number is prime.
// Returns: 1 = Yes, 0 = No.
{
	int_t i = 2;
	if (n < 2)
		return 0;
	while (i * i <= n)
	{
		if (!(n % i ++))
			return 0;
	}
	return 1;
} /* is prime */

static int_t primenumber (int_t n)
// Returns the smallest prime number
// greater than or equal to the given one.
{
	while (!isprime (n))
		++ n;
	return n;
} /* prime number */

// --------------------------------------------------

SetOfBitFields::SetOfBitFields (int_t len, int_t maxelem): values ()
{
	if (len <= 0)
		len = 0;
	if (!len)
		maxelem = 0;
	length = len;
	avail = maxelem;
	usedcount = 0;
	if (maxelem)
	{
		size = primenumber (maxelem + (maxelem >> 3));
		bf = new BitField [size];
		buf = new unsigned char [((length + 7) >> 3) * avail];
		if (!bf || !buf)
			throw "Not enough memory for a bit field set.";
		values. allocate (size);
	}
	else
	{
		size = 0;
		bf = NULL;
		buf = NULL;
	}
	bufcur = buf;
	return;
} /* SetOfBitFields::SetOfBitFields */

int SetOfBitFields::add (const BitField &b, int value)
{
	if (!avail)
		return -1;
	int_t pos = b. hashkey (length) % size;
	if (pos < 0)
		pos = -(pos + 1);
	int_t add = 0;
	while (bf [pos]. defined ())
	{
		if (thesame (bf [pos], b, length))
			return values. test (pos);
		if (!add)
		{
			add = b. hashadd (length) % size;
			if (!add)
				add = 1;
		}
		pos += add;
		if ((pos >= size) || (pos < 0))
			pos -= size;
	}
	bf [pos]. define (bufcur, length);
	bufcur += (length + 7) >> 3;
	bf [pos]. takebits (b, length);
	if (value)
		values. set (pos);
	avail --;
	usedcount ++;
	return 2;
} /* SetOfBitFields::add */

int SetOfBitFields::check (const BitField &b) const
{
	if (!size)
		return -1;
	int_t pos = b. hashkey (length) % size;
	if (pos < 0)
		pos = -(pos + 1);
	int_t add = 0;
	while (bf [pos]. defined ())
	{
		if (thesame (bf [pos], b, length))
			return values. test (pos);
		if (!add)
		{
			add = b. hashadd (length) % size;
			if (!add)
				add = 1;
		}
		pos += add;
		if ((pos >= size) || (pos < 0))
			pos -= size;
	}
	return -1;
} /* SetOfBitFields::check */


} // namespace homology
} // namespace capd

/// @}

