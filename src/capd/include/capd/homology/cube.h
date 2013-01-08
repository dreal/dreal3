/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cube.h
///
/// This file includes header files with various definitions of full cubes
/// and defines the standard types for most commonly used structures
/// related to full cubes.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: October 25, 2005.


#ifndef _CAPD_HOMOLOGY_CUBE_H_ 
#define _CAPD_HOMOLOGY_CUBE_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cubemain.h"
#include "capd/homology/cubebase.h"
#include "capd/homology/cubefix.h"
#include "capd/homology/cubevar.h"

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstring>


namespace capd {
namespace homology {


/// The default cube type.
typedef tCubeBase<coordinate> Cube;

/// An alternative name for a cube.
typedef Cube FullCube;

/// An alternative name for a cube.
typedef Cube HyperCube;

/// The default type of a set of cubes.
typedef hashedset<Cube> SetOfCubes;

/// The default type of a combinatorial cubical multivalued map.
/// This is a map which assigns a set of cubes to each cube in its domain.
typedef mvmap<Cube,Cube> CombinatorialMultivaluedMap;

/// A lower-case name of a cube [deprecated].
typedef Cube cube;

/// An abbreviation for a set of cubes [deprecated].
typedef SetOfCubes cubes;

/// An abbreviation for a combinatorial cubical multivalued map.
typedef CombinatorialMultivaluedMap CubicalMap;

/// A lower-case version of the name of a combinatorial cubical
/// multivalued map [deprecated].
typedef CombinatorialMultivaluedMap cubicalmap;


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CUBE_H_ 

/// @}

