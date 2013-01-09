/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file randomCubSet.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2007
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_RANDOM_CUBSET_H_)
#define _RANDOM_CUBSET_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <new>
using namespace std;

#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"
#include "capd/auxil/stringOstream.h"
#include "capd/auxil/random.h"
#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"
#include "capd/bitSet/EuclBitSet.h"

template <int dim>
void generate(const char* A_fileName, int A_size, double A_frequency){
  typedef CubSetT<EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,dim> > BCubSet;
  typedef typename BCubSet::BitCoordIterator BitCoordIterator;
  BCubSet cubSet(A_size);
  BitCoordIterator it(cubSet);
  cubSet.clear();
  for(it=cubSet.begin();it<cubSet.end();++it){
    if(it[0]>A_size-1) continue;   // skip points in the padded part
    if( random(1.0) < A_frequency ) it.setBit();
  }
  unsigned int repsetType='D'*256+'B';
  cubSet.writeBmp(A_fileName,repsetType);
  std::cout << "Generated " << dim << " dim set " << " of " << cubSet.cardinality() << " cubes\n" <<
     " with enclosing box ";
  for(int i=0;i<dim;++i) std::cout << cubSet.getUnpaddedWidth(i) << " ";
  std::cout  << std::endl;
}

void generate(const char* A_fileName, int A_dim, int A_size, double A_frequency){
  switch(A_dim){
    case 2: generate<2>(A_fileName,A_size,A_frequency);
            return;
    case 3: generate<3>(A_fileName,A_size,A_frequency);
            return;
    case 4: generate<4>(A_fileName,A_size,A_frequency);
            return;
    case 5: generate<5>(A_fileName,A_size,A_frequency);
            return;
    case 6: generate<6>(A_fileName,A_size,A_frequency);
            return;
    case 7: generate<7>(A_fileName,A_size,A_frequency);
            return;
    case 8: generate<8>(A_fileName,A_size,A_frequency);
            return;
    case 9: generate<9>(A_fileName,A_size,A_frequency);
            return;
    case 10: generate<10>(A_fileName,A_size,A_frequency);
            return;
    case 11: generate<11>(A_fileName,A_size,A_frequency);
            return;
    case 12: generate<12>(A_fileName,A_size,A_frequency);
            return;
    default:;
  }
}

#endif //_RANDOM_CUBSET_H_
/// @}

