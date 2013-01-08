/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bitcode.h
///
/// This file contains the declaration of functions for reading and writing
/// full cubical sets encoded in the text format as bit codes used in the
/// "chom" program written by Bill Kalies.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 12, 2001. Last revision: August 16, 2007.


#ifndef _CAPD_HOMOLOGY_BITCODE_H_ 
#define _CAPD_HOMOLOGY_BITCODE_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"

#include <iostream>
#include <fstream>
#include <ctime>
#include <cstdlib>

namespace capd {
namespace homology {


// --------------------------------------------------
// --------------------- BITCODE --------------------
// --------------------------------------------------

/// Reads a set of full cubical sets represented as a set of points
/// from a file encoded in the "bitcode" format used by Bill Kalies.
/// The depth of bit codes is saved to '*bitcode_depth' unless NULL.
/// Returns 0 on success and -1 on error (and displays a message).
int readbitpoints (std::istream &in, pointset &p, int *bitcode_depth = NULL);

/// Writes a full cubical set represented by a set of points to a file
/// in the "bitcode" format.
/// If 'sorted', bit codes are sorted as the software by Bill Kalies needs.
/// Otherwise they are saved in the same order as the points in 'p'.
/// The depth of bit fields is determined automatically to the minimal
/// necessary value unless 'fixed_depth' is positive.
/// As the lower left corner, the minimal coordinates of the points are
/// selected unless 'fixed_corner' is NULL.
/// Returns 0 on success and -1 on error (and displays a message).
int writebitpoints (std::ostream &out, pointset &p, bool sorted = true,
	int fixed_depth = 0, coordinate *fixed_corner = NULL);


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_BITCODE_H_ 

/// @}

