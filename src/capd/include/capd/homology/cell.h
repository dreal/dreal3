/// @addtogroup homology
/// @{

/////////////////////////////////////////////////////////////////////////////
///
/// @file cell.h
///
/// This file includes header files with various definitions of cubical
/// cells and defines the standard types for most commonly used structures
/// related to cubical cells.
///
/// @author Pawel Pilarczyk
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 1997-2010 by Pawel Pilarczyk.
//
// This file constitutes a part of the Homology Library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Started in January 2002. Last revision: November 5, 2004.


#ifndef _CAPD_HOMOLOGY_CELL_H_ 
#define _CAPD_HOMOLOGY_CELL_H_ 

#include "capd/homology/config.h"
#include "capd/homology/textfile.h"
#include "capd/homology/pointset.h"
#include "capd/homology/chains.h"
#include "capd/homology/bitfield.h"
#include "capd/homology/integer.h"
#include "capd/homology/hashsets.h"
#include "capd/homology/gcomplex.h"
#include "capd/homology/pointbas.h"
#include "capd/homology/cellmain.h"
#include "capd/homology/cellbase.h"
#include "capd/homology/cellfix.h"
#include "capd/homology/cellvar.h"

#include <iostream>
#include <fstream>
#include <cstdlib>

namespace capd {
namespace homology {


/// The default type of a cubical cell.
typedef tCellBase<coordinate> CubicalCell;

/// An alternative name for a cubical cell.
typedef CubicalCell ElementaryCell;

/// The default type of a set of cubical cells.
typedef hashedset<CubicalCell> SetOfCubicalCells;

/// The default type of a cubical complex.
typedef gcomplex<CubicalCell,integer> CubicalComplex;

/// The default type of a cubical multivalued map. The image of each
/// cubical cell is a set of cubical cells.
typedef mvcellmap<CubicalCell,integer,CubicalCell> CubicalMultivaluedMap;


/// An abbreviation for a cubical cell [deprecated].
typedef CubicalCell qcell;

/// An abbreviation for a set of cubical cell [deprecated].
typedef SetOfCubicalCells qcells;

/// An abbreviation for a cubical complex [deprecated].
typedef CubicalComplex cubicalcomplex;


} // namespace homology
} // namespace capd

#endif // _CAPD_HOMOLOGY_CELL_H_ 

/// @}

