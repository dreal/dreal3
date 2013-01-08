/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file bitSetTypes.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 





#if !defined(_BITSETTYPES_H)
#define _BITSETTYPES_H

#include "capd/auxil/CRef.h"

typedef unsigned long int cluster;
typedef BitSetT<BitmapT<cluster> > BitSet;
typedef EuclBitSetT<BitSet,embeddingDim> EuclBitSet;
typedef CubSetT<EuclBitSet> BCubSet;
typedef CubCellSetT<EuclBitSet> BCubCelSet;
typedef CRef<BCubSet> BCubSetCR;
typedef CRef<BCubCelSet> BCubCelSetCR;

#endif //_BITSETTYPES_H

/// @}

