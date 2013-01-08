/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrHomology.hpp
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

#include "capd/homologicalAlgebra/acyclicConfigs.hpp"
#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubFile.hpp"
#include "capd/homologicalAlgebra/readCubCellSet.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.hpp" // temporarily here, should be compiled into the library
#include "capd/repSet/ECell3dCode.h"

void CrHom(int embDim, const int dims[], const char* bytes, int* betti,int streaming){
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
  CRef<HomologySignature<int> > homSignCR=CubSetFunctors<BCubSet,BCubCelSet>::HomSignViaRepSetReductions(cubSetCR);
  for(int i=0;i<embeddingDim;++i) betti[i]=homSignCR().bettiNumber(i);
}

// Note: only one of the two following methods may be uncommented

// This method kept only for testing purposes for the above version of CrHom
/* // -------------- keep it here ------------
void CrHom(const char* fileName){
  int d[3];
  const int* dims=d;
  const char* bitmap=0;
  int betti[3];
  // The CR reference is stored in cubSetCR to avoid premature destroying of the bitmap
  CRef<BCubSet> cubSetCR=readCubFile(fileName,dims,bitmap);
  CrHom(embeddingDim,dims,bitmap,betti,false);
  for(int i=0;i<embeddingDim;++i) std::cout << "Betti[" << i << "]=" << betti[i]  << std::endl;
}
*/ // -------------- keep it here ------------

//typedef ECell3dCode ElementaryCellType;  // This in theory is quicker but the class is only for embDim=3 so far
typedef ElementaryCell ElementaryCellType;

typedef int ScalarType;
typedef capd::vectalg::Matrix<ScalarType,0,0> MatrixType;
typedef FreeModule<ElementaryCellType,MatrixType> FreeModuleType;
typedef FreeChainComplex<FreeModule<ElementaryCellType,MatrixType> > FreeChainComplexType;
typedef CubSetFunctors<BCubSet,BCubCelSet,FreeChainComplexType> CubSetFunctorsType;

void CrHom(const char* fileName){

//  CRef<BCubSet> cubSetCR=readCubFile<BCubSet>(fileName); // This version changed cubcellset to cubset and then again to cubcellset, which unnecessarily increased the size of the set
  CRef<BCubCelSet> cubCellSetCR=readCubCellSet<BCubSet,BCubCelSet>(fileName);
  // -- MM  std::cout << "Read cubCellSetCR()=\n" << cubCellSetCR() << std::endl;
/*
cubCellSetCR().rescale(2);
BCubCelSet cubCelSetCopy(cubCellSetCR()); // copy needed, because for some reason writing destroys the set
unsigned int repsetType='R'*256+'B'; // for representable sets
cubCelSetCopy.writeBmp("rescaled.bmd",repsetType);
std::cout << "Got " << cubCellSetCR().cardinality() << " cells" << std::endl;  // -- MM
*/
  Stopwatch swTot;
  CRef<HomologySignature<int> > homSignCR=CubSetFunctorsType::HomSignViaRepSetReductions(cubCellSetCR);
//  CRef<HomologySignature<int> > homSignCR=CubSetFunctorsType::HomSignViaRepSetReductions(cubSetCR);
//  CRef<HomologySignature<int> > homSignCR=CubSetFunctorsType::HomSignViaRepSetReductionsNew(cubSetCR);
  fcout << "Computation completed in " << swTot  << std::endl;
  fcout << "Computed homology is: \n\n" << homSignCR()  << std::endl;
}
/// @}

