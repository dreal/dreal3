/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file known.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: June 2, 2007.


#include "capd/homology/known.h"

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------------- BitFields --------------------
// --------------------------------------------------

BitFields::~BitFields ()
{
	for (int i = 0; i < len; i ++)
	{
		if (tab [i])
			delete tab [i];
	}
	if (len)
	{
		delete [] tab;
		delete [] maxkb;
	}
	return;
} /* BitFields::~BitFields */

void BitFields::extend (int n)
{
	// if there is no need to extend the tables, do nothing
	if (n <= len)
		return;

	// allocate new tables
	SetOfBitFields **newtab = new SetOfBitFields * [n];
	int *newmaxkb = new int [n];
	if (!newtab || !newmaxkb)
		throw "Can't extend the table of bitfields.";

	// copy the old tables
	int i;
	for (i = 0; i < len; i ++)
	{
		newtab [i] = tab [i];
		newmaxkb [i] = maxkb [i];
	}

	// initialize the new entries of the tables
	for (i = len; i < n; i ++)
	{
		newtab [i] = NULL;
		newmaxkb [i] = maxkb ? maxkb [0] : -1;
	}

	// deallocate the previous tables
	if (len)
	{
		delete [] tab;
		delete [] maxkb;
	}

	// assign the new values to the data structures
	len = n;
	tab = newtab;
	maxkb = newmaxkb;
	return;
} /* BitFields::extend */

void BitFields::setkblimit (int limit, int dim)
{
	// if no limit is given, do nothing
	if (limit < 0)
		return;

	// extend the tables if necessary
	if (dim >= len)
		extend (dim + 1);

	// set the default limit for every dimension if requested to
	if (dim <= 0)
	{
		if (!len)
			extend (1);
		for (int i = 0; i < len; i ++)
			if ((dim < 0) || (maxkb [i] < 0))
				maxkb [i] = limit;
	}
	// otherwise, set the limit for the given dimension
	else
		maxkb [dim] = limit;

	return;
} /* BitFields::setkblimit */

int BitFields::getkblimit (int dim) const
{
	// if no bit field sets are defined, then there is no limit
	if (!len)
		return -1;

	// if the dimension is too high, return the default limit
	else if (dim >= len)
		return maxkb [0];

	// if the dimension given is negative, return default limit
	else if (dim < 0)
		return maxkb [0];

	// otherwise, return the limit for the given dimension
	else
		return maxkb [dim];
} /* BitFields::getkblimit */

void BitFields::forget (int dim)
{
	// if the dimension is out of range, there is nothing to be forgotten
	if (dim >= len)
		return;

	// if the dimension is negative, forget everything
	if (dim < 0)
	{
		for (int i = 0; i < len; i ++)
			forget (i);
		return;
	}

	// if there is not bit field set, do nothing
	if (!tab [dim])
		return;

	// display the bit field usage
	if (tab [dim] -> used ())
		sout << tab [dim] -> used () <<
			" bit fields for dimension " << dim <<
			" were used.\n";

	// forget the given table
	delete tab [dim];
	tab [dim] = NULL;

	return;
} /* BitFields::forget */

void BitFields::allocate (int dim)
{
	// if the dimension is out of range, do nothing
	if (dim < 0)
		return;

	// extend the tables if necessary
	extend (dim + 1);

	// determine the number of bits to be allocated in each bit field
	int maxXneighbors = 1;
	for (int i = 0; i < dim; i ++)
		maxXneighbors *= 3;
	maxXneighbors --;

	// determine a recommended number of bit fields to be allocated
	int recommended [] = {0, 10, 300, 50000, 200000};
	int nXbits = (dim < 5) ? recommended [dim] :
		(((dim + dim / 2) * 1024 * 1024) /
		((maxXneighbors + 7) / 8));

	// adjust the number of bit fields to fit the memory limit
	int memorylimit = maxkb [dim];
	if (memorylimit >= 0)
		nXbits = 1024 * memorylimit /
			((maxXneighbors + 7) / 8);

	// delete the previously allocated set of bit fields if any
	if (tab [dim])
		forget (dim);

	// allocate the set of bit fields
	tab [dim] = nXbits ?
		new SetOfBitFields (maxXneighbors, nXbits) : NULL;

	// show a message of what has been done
	if (nXbits)
		sout << nXbits << " bit fields allocated (" <<
			((((maxXneighbors + 7) / 8) * nXbits + 512 * 1024) /
			1024 / 1024) << " MB) to speed up " << dim <<
			"-dimensional reduction.\n";
	return;
} /* BitFields::allocate */

// the global table of BitFields which store the acyclicity information
BitFields knownbits;

// a special object which will deallocate any left bit field sets
// and display statistics (if necessary) at the program's termination
/*
class KnownBitsDeallocator
{
public:
	KnownBitsDeallocator () {return;};
	~KnownBitsDeallocator () {knownbits. forget (); return;}

} theKnownBitsDeallocator;
*/


} // namespace homology
} // namespace capd

/// @}

