/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file randomCubCellSet.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2007
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_RANDOM_CUBCELLSET_H_)
#define _RANDOM_CUBCELLSET_H_

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


#include "capd/bitSet/CubCellSetT.hpp"

template <int dim>
void generate(const char* A_fileName, int A_size, double A_frequency){
  typedef CubCellSetT<EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,dim> > BCubCelSet;
  typedef typename BCubCelSet::BitCoordIterator BitCoordIterator;
  BCubCelSet cubCellSet(2*A_size+1,true);
  BitCoordIterator it(cubCellSet);
  for(it=cubCellSet.begin();it<cubCellSet.end();++it){
    if(it[0]>2*A_size) goto skip;
    for(int i=0;i<dim;++i){
      if(/* it[i]<=0 || it[i]>=dim-1 || */ it.odd(i)) goto skip;  // skip collar and cells of dim>0
    }
    if( random(1.0) < A_frequency ) it.setBit();
    skip:;
  }
  cubCellSet.cubicalClosureSkeleton(dim);
  unsigned int repsetType='R'*256+'B';
  cubCellSet.writeBmp(A_fileName,repsetType);
  std::cout << "Generated " << dim << " dim set " << " of " << cubCellSet.cardinality() << " cells\n" <<
     " with enclosing box ";
  for(int i=0;i<dim;++i) std::cout << cubCellSet.getUnpaddedWidth(i) << " ";
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

#endif //_RANDOM_CUBCELLSET_H_
/// @}

