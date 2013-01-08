/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file tabulate.cpp
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: July 21, 2010.


#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/chains.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/gcomplex.h"
#include "capd/homology/cubisets.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <ctime>
#include <cstdlib>
#include <cctype>

namespace capd {
namespace homology {


// --------------------------------------------------
// ------------ tabulated neighborhoods -------------
// --------------------------------------------------

char tabulated1d [] = {'\x06'};

char tabulated2d [] =
{
	'\xf6', '\xf3', '\xf5', '\xf0', '\x6f', '\x6a', '\x6c', '\x68',
	'\xa3', '\xa2', '\xa0', '\xa0', '\x6f', '\x6a', '\x6c', '\x68',
	'\xc5', '\xc0', '\xc4', '\xc0', '\x6f', '\x6a', '\x6c', '\x68',
	'\x80', '\x80', '\x80', '\x80', '\x6f', '\x6a', '\x6c', '\x68',
};

Tabulated::Tabulated ()
{
	int three = 1;
	for (int dim = 0; dim < maxdim; ++ dim)
	{
		if (dim == 0)
			size [dim] = 0;
		else if (dim == 1)
			size [dim] = 1;
		else
		{
			size [dim] = static_cast<int_t> (1) <<
				(three - 1 - 3);
		}
		deallocate [dim] = false;
		tables [dim] = 0;
	//	sout << "DEBUG: Dim " << dim << ": " << size [dim] <<
	//		" byte(s), " << (three - 1) << " neighbors.\n";
		three *= 3;
	}
	define (1, tabulated1d);
	define (2, tabulated2d);
	return;
} /* Tabulated::Tabulated */

Tabulated::~Tabulated ()
{
	for (int i = 0; i < maxdim; ++ i)
		if (tables [i] && deallocate [i])
			delete [] (tables [i]);
	return;
} /* Tabulated::Tabulated */

int Tabulated::read (int dim, const char *filename)
{
	if ((dim <= 0) || (dim >= maxdim))
		return -1;
	if (!tables [dim] || !deallocate [dim])
	{
		tables [dim] = new char [size [dim]];
		deallocate [dim] = true;
	}
	std::ifstream f;
	f. open (filename, std::ios::in | std::ios::binary);
	f. read (tables [dim], size [dim]);
	if (!f)
		return -1;
	return 0;
} /* Tabulated::read */

int Tabulated::write (int dim, const char *filename) const
{
	if ((dim <= 0) || (dim >= maxdim) || (!tables [dim]))
		return -1;
	std::ofstream f;
	f. open (filename, std::ios::out | std::ios::binary);
	f. write (tables [dim], size [dim]);
	if (!f)
		return -1;
	return 0;
} /* Tabulated::write */

int Tabulated::compute (int dim)
{
	// if the dimension is wrong, do nothing
	if ((dim <= 0) || (dim >= maxdim))
		return -1;

	// allocate memory for the table if necessary
	if (!tables [dim])
	{
		tables [dim] = new char [size [dim]];
		deallocate [dim] = true;
	}

	// remember the memory buffer and temporarily set no tabulating
	char *thetable = tables [dim];
	tables [dim] = 0;

	// clear the entire table
	for (int_t i = 0; i < size [dim]; ++ i)
		thetable [i] = 0;

	// prepare a bit field
	int_t maxneighbors = getmaxneighbors (dim);
	int_t nconfigs = static_cast<int_t> (1) << maxneighbors;
	BitField b;
	b. allocate (maxneighbors);

	// prepare a temporary cube
	coordinate c [Cube::MaxDim];
	for (int i = 0; i < dim; ++ i)
		c [i] = 0;
	Cube qzero (c, dim);

	// compute all the configurations
	sout << "Computing " << dim << "-dimensional configurations... ";
	for (int_t i = 1; i < nconfigs; ++ i)
	{
		int2bits (i, maxneighbors, b);
	//	gcomplex<CubicalCell,integer> neighbors;
	//	addneighbors (qzero, b, neighbors, true);
	//	if (acyclic (neighbors))
		SetOfCubes neighbors;
		addneighbors (qzero, b, neighbors, true);
		if (acyclic (qzero, dim, neighbors, &b, maxneighbors))
			Tabulated::set (thetable, i);
		if (!(i % 153791))
			scon << std::setw (12) << i <<
				"\b\b\b\b\b\b\b\b\b\b\b\b";
	}
	sout << "Completed successfully.\n";

	// deallocate the bit field
	b. free ();

	// set the tabulating table to the just computed one
	tables [dim] = thetable;
	return 0;
} /* Tabulated::compute */

// --------------------------------------------------

Tabulated tabulated;


} // namespace homology
} // namespace capd

// --------------------------------------------------


/// @}

