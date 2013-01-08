/// @addtogroup struct
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file bitcount.h
///
/// This file defines a very simple function for counting the number of bits
/// in a byte or a multi-byte integer.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on November 29, 2005. Last revision: November 29, 2005.


#ifndef _CAPD_HOMOLOGY_BITCOUNT_H_ 
#define _CAPD_HOMOLOGY_BITCOUNT_H_ 

namespace capd {
namespace homology {


extern unsigned char bitcounttable [];

inline int bitcountbyte (char n)
{
	return bitcounttable [static_cast<unsigned char> (n)];
} /* bitcountbyte */

inline int bitcount (int number)
{
	if (!number)
		return 0;
	unsigned int n = static_cast<unsigned int> (number);
	if (n < 256)
		return bitcountbyte (static_cast<unsigned char> (n));
	int c = 0;
	while (n > 255)
	{
		if (n & 1)
			++ c;
		n >>= 1;
	}
	return c + bitcountbyte (static_cast<unsigned char> (n));
} /* bitcount */


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_BITCOUNT_H_ 

/// @}

