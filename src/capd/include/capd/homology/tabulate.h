/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file tabulate.h
///
/// This file contains the definition of a class which stores
/// tabulated configuration of full cubical neighborhoods
/// used in the cubical reduction procedures.
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


#ifndef _CAPD_HOMOLOGY_TABULATE_H_ 
#define _CAPD_HOMOLOGY_TABULATE_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {

/// A class for storing tabulated configurations of neighbors
/// for various dimensions.
class Tabulated
{
public:
	/// The default constructor.
	Tabulated ();

	/// The destructor.
	~Tabulated ();

	/// Reads tabulated configurations from a file.
	int read (int dim, const char *filename);

	/// Writes tabulated configurations to a file.
	int write (int dim, const char *filename) const;

	/// Computes tabulated configurations for a specific dimension.
	int compute (int dim);

	/// Sets tabulated configuration bits to a given table.
	/// Note: This buffer will not be deallocated automatically.
	/// Call this function with the null pointer to disable the table.
	int define (int dim, char *buffer);

	/// Retrieves the buffer allocated for the specific dimension
	/// or returns the null pointer if none.
	const char *operator [] (int dim) const;

	/// Retrieve the given bit from the given table.
	static int get (const char *table, int_t bitnumber);

	/// Sets the given bit in the given table.
	static void set (char *table, int_t bitnumber);

private:
	/// The strict upper bound for the supported dimensions.
	static const int maxdim = 8;

	/// The tabulated configurations.
	char *tables [maxdim];

	/// Should the configuration tables be deallocated?
	bool deallocate [maxdim];

	/// The size of the table in bytes for each dimension.
	int size [maxdim];
	
}; /* Tabulated */

// --------------------------------------------------

inline int Tabulated::define (int dim, char *buffer)
{
	if ((dim <= 0) || (dim >= maxdim))
		return -1;
	if (tables [dim] && deallocate [dim])
	{
		delete [] (tables [dim]);
		deallocate [dim] = false;
	}
	tables [dim] = buffer;
	return 0;
} /* Tabulated::define */

inline const char *Tabulated::operator [] (int dim) const
{
	if ((dim <= 0) || (dim >= maxdim))
		return 0;
	else
		return tables [dim];
} /* Tabulated::operator [] */

inline int Tabulated::get (const char *table, int_t bitnumber)
{
	if (table [bitnumber >> 3] & (1 << (bitnumber & 0x07)))
		return 1;
	else
		return 0;
} /* Tabulated::get */

inline void Tabulated::set (char *table, int_t bitnumber)
{
	table [bitnumber >> 3] |=
		static_cast<char> (1 << (bitnumber & 0x07));
	return;
} /* Tabulated::set */

// --------------------------------------------------

/// The global instance of this class which stores tabulated configurations
/// to use in the full cube reduction procedures.
extern Tabulated tabulated;


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_TABULATE_H_ 

/// @}

