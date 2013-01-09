/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cubdemo.h
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started on February 15, 2003. Last revision: September 6, 2003.


#ifndef _CAPD_HOMOLOGY_CUBDEMO_H_ 
#define _CAPD_HOMOLOGY_CUBDEMO_H_ 

#include "capd/homology/homology.h"

using namespace capd::homology;


// --------------------------------------------------
// -------------------- READ MAP --------------------
// --------------------------------------------------

// Read a map from the given file.
void readmap (const char *filename, cubicalmap &F, const char *name);


// --------------------------------------------------
// ------------------- INCLUSIONS -------------------
// --------------------------------------------------

// Reduce the full-dimensional sets of cubes in such a way that
// no information is lost if one is interested in computing the homomorphisms
// induced in homology by the inclusion maps between the subsequent sets.
// Note: The sets are modified such that they form an ascending sequence.
void ReduceFullDimCubes (cubes Xcubes [], cubes Acubes [], int n);

// Compute the homomorphisms induced in homology by the inclusion maps
// of the pairs of sets (X [i], A [i]) into (X [i + 1], A [i + 1]).
// Allocate tables of chain complexes representing the homology of each
// set or pair of sets and allocate maps induced in homology between them.
// Store the generators of each pair into the corresponding table
// of cubical complexes.
void InclusionMapsHomology (cubes Xcubes [], cubes Acubes [],
	int n, chaincomplex<integer> **&homology,
	chainmap<integer> **&inclusions,
	multitable<cubicalcomplex> generators []);

#endif // _CAPD_HOMOLOGY_CUBDEMO_H_ 

/// @}

