/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_UL_lowDim.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#include "capd/bitSet/BitmapT.h"
#include "capd/bitSet/BitSetT.h"
#include "capd/bitSet/EuclBitSetT.hpp"
#include "capd/bitSet/selector.h"

typedef unsigned long int cluster;
typedef BitSetT<BitmapT<cluster> > BitSet;

#define SETUP(dim) \
typedef EuclBitSetT<BitSet,dim> EuclBitSetD##dim; \
template class EuclBitSetT<BitSet,dim>;   \
template std::istream& operator>> <BitSet,dim>(std::istream& in,EuclBitSetD##dim&);  \
template EuclBitSetT<BitSet,dim>& EuclBitSetT<BitSet,dim>::add<HiperSurfSelector>(const HiperSurfSelector&,bool);

SETUP(2)
SETUP(3)
SETUP(4)
SETUP(5)
SETUP(6)
SETUP(7)
SETUP(8)
SETUP(9)
SETUP(10)
SETUP(11)
SETUP(12)
SETUP(13)
SETUP(14)

#undef SETUP

