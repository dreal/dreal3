/// @addtogroup HomologyEngines
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file homengin/homology.h
///
/// This file defines a top-level interface to a homology computation
/// procedure of full cubical sets represented in terms of a bitmap.
/// Several algorithms (engines) can be used, either selected by the user,
/// or chosen automatically in a heuristic way, depending on the data type.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on March 19, 2006. Last revision: July 27, 2007.


#ifndef _CAPD_HOMENGIN_HOMOLOGY_H_ 
#define _CAPD_HOMENGIN_HOMOLOGY_H_ 

#include <string>
#include <cstring>
#include "capd/homengin/engines.h"


/// Computes the Betti numbers of the given set of full cubes
/// encoded in a binary bitmap.
/// \param buffer - a buffer that contains the bitmap which defines the cubes;
/// each byte stores 8 subsequent positions, with lower bits corresponding to
/// cubes placed to the left from the higher bits; the width of each line
/// must be a multiple of 4 bytes (if the number of cubes is less than that,
/// then the lines must be padded with zeros) - this is required by the MM*
/// engines; the first line corresponds to pixels with the coordinates
/// (0,0,0,...,0), (1,0,0,...,0), ..., (n,0,0,...,0); the next line in the
/// bitmap corresponds to the pixels (0,1,0,...,0), ..., (n,1,0,...,0), etc.
/// \param sizes - a table of the sizes of the bitmap in each direction,
/// \param dim - the space dimension,
/// \param result - a table into which the result is written; its size
/// must be at least (<i>dim</i> + 1),
/// \param engine - the name of a homology engine to choose; the engine is
/// automatically selected if this is zero
/// \param wrapping - space wrapping in each direction (0 = no wrapping)
/// \param quiet - true = the function should display no messages
/// to the standard output stream; false = show a lot of messages
inline void ComputeBettiNumbers (const void *buffer, int *sizes, int dim,
	int *result, const char *engine = 0, const int *wrapping = 0,
	bool quiet = false)
{
	using namespace capd::homology;
	// turn off screen output if requested to
	bool soutput = sout. show;
	bool coutput = scon. show;
	if (quiet)
	{
		sout. show = false;
		scon. show = false;
		fcout. turnOff ();
	}
	else
		fcout. turnOn ();

	// create a corresponding set of cubes
	capd::homengin::cubitmap X (reinterpret_cast<const char *> (buffer),
		sizes, dim);

	// set the space wrapping
	if (wrapping)
		X. setwrapping (wrapping, dim);

	// find the best engine to use for the homology computation
	const capd::homengin::engine *e;
	if (!engine)
		e = capd::homengin::engine::find (&X);

	// another possibility: find the engine with the given name
	else
		e = capd::homengin::engine::find (engine);

	// compute the homology of the set of cubes
	capd::homengin::algstruct<capd::homology::integer> hom;
	e -> homology (X, hom);
	sout << "The computed homology is " << hom << ".\n";

	// fill in the resulting table of Betti numbers
	int levels = hom. countLevels ();
	for (int i = 0; i <= dim; ++ i)
		result [i] = (i < levels) ? hom. getBetti (i) : 0;

	// restore the message settings
	capd::homology::sout. show = soutput;
	capd::homology::scon. show = coutput;
	return;
} /* ComputeBettiNumbers */


// *** temporarily ***
#include "capd/homengin/cubiset.h"


#endif // _CAPD_HOMENGIN_HOMOLOGY_H_ 

/// @}

