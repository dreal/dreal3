/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file known.h
///
/// This file contains the definition of a tabulated set of configurations
/// of full cubical neighborhood used for reducing full cubical sets
/// in the homology computation procedures.
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


#ifndef _CAPD_HOMOLOGY_KNOWN_H_ 
#define _CAPD_HOMOLOGY_KNOWN_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/bitfield.h"

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------------- BitFields --------------------
// --------------------------------------------------

/// This class defines a simple table of bit fields with very limited
/// functionality that is used for storing the information
/// on the verified combinations of cubes' neighbors.
class BitFields
{
public:
	/// The default constructor.
	BitFields ();

	/// The destructor.
	~BitFields ();

	/// Sets the limit for the number of kilobytes used for BitFields.
	/// The limit applied to dimension < 0 is copied to all the
	/// others and can be retrieved as the limit for dimension 0.
	/// The limit for dim. 0 is the default if not defined otherwise.
	void setkblimit (int limit = -1, int dim = -1);

	/// Returns the current limit for the given dimension.
	int getkblimit (int dim = 0) const;

	/// Returns the corresponding bit field set and allocates it if not
	/// used so far. If no bit field set is in use, returns 0.
	SetOfBitFields *operator [] (int dim);

	/// Forgets the given bit field set or all the sets.
	void forget (int dim = -1);

private:
	/// The table of bit field sets for each dimension.
	SetOfBitFields **tab;

	/// The length of the currently allocated table.
	int len;

	/// The memory limit for each table (in kilobytes), -1 for none.
	int *maxkb;

	/// Extends the table to the given length if necessary.
	void extend (int n);

	/// Allocates the specific bit field set.
	void allocate (int dim);

}; /* class BitFields */

// --------------------------------------------------

inline BitFields::BitFields ()
{
	tab = NULL;
	len = 0;
	maxkb = NULL;
	return;
} /* BitFields::BitFields */

inline SetOfBitFields *BitFields::operator [] (int dim)
{
	// make sure the dimension is positive
	if (dim <= 0)
		throw "Trying to get a bit field set of non-positive dim.";

	// extend the tables if necessary
	if (dim >= len)
		extend (dim + 1);

	// allocate the bit field set if necessary
	if (!tab [dim] && maxkb [dim])
		allocate (dim);

	// return the pointer to the requested bit field set
	return tab [dim];
} /* BitFields::operator [] */

// --------------------------------------------------

/// The global table of BitFields which store the acyclicity information
/// for reducing full cubical sets.
extern BitFields knownbits;


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_KNOWN_H_ 

/// @}

