/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ArHomology.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <stdexcept>
#include <new>
using namespace std;

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"

extern ofstreamcout fcout;

#include "capd/vectalg/MatrixSlice.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"

using namespace capd;
using namespace matrixAlgorithms;

#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubFile.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
//#include "homologicalAlgebra/acyclicConfigs.hpp"  // Temporary solution: somewhere the acyclicConfigsD3 table is unnecessarily referenced!!!

void ArHom(int embDim, const int dims[], const char* bytes, int* betti,int streaming){
  if(streaming) fcout.turnOn();
  else fcout.turnOff();
  if(embeddingDim != embDim){
    std::ostringstream s;
    std::cout  << "This executable is for embedding dimension " << embeddingDim << " and the provided set has dimension " << embDim  << std::endl;
    s << "This executable is for embedding dimension " << embeddingDim << " and the provided set has dimension " << embDim  << std::endl;
    throw std::runtime_error(s.str());
  }
  if(dims[0] % 32) throw std::runtime_error("The 0th dimension must be a multiciplity of 32!");
  CRef<BCubSet> cubSetCR(new BCubSet(dims,bytes));
  CRef<HomologySignature<int> > homSignCR=CubSetFunctors<BCubSet,BCubCelSet>::HomologyViaAlgebraicReductions(cubSetCR);
  for(int i=0;i<embeddingDim;++i) betti[i]=homSignCR().bettiNumber(i);
}

// Note: only one of the two following methods may be uncommented

// This method kept only for testing purposes for the above version of ArHom
/* // -------------- keep it here ------------
void ArHom(const char* fileName){
  int d[3];
  const int* dims=d;
  const char* bitmap=0;
  int betti[3];
  readCubFile(fileName,dims,bitmap);
  ArHom(embeddingDim,dims,bitmap,betti,false);
  for(int i=0;i<embeddingDim;++i) std::cout << "Betti[" << i << "]=" << betti[i]  << std::endl;
}
*/ // -------------- keep it here ------------

void ArHom(const char* fileName){
  CRef<BCubSet> cubSetCR=readCubFile<BCubSet,BCubCelSet>(fileName);
  Stopwatch swTot;
  CRef<HomologySignature<int> > homSignCR=CubSetFunctors<BCubSet,BCubCelSet>::HomologyViaAlgebraicReductions(cubSetCR);
  fcout << "Computed homology is: \n\n" << homSignCR()  << std::endl;
  fcout << "Computation completed in " << swTot  << std::endl;
}
/// @}

