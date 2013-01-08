/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrbHomology.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*
    This is the version of the CrHomology.hpp file adapted to compute
    not only Betti and torsion numbers but also the homology basis
*/

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
#include "capd/homologicalAlgebra/readCubCellSet.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
#include "capd/homologicalAlgebra/acyclicConfigs.hpp"

//#include "bitSet/CubCellSetSimplificatorT.h"
#include "capd/bitSet/ReductionPairT.h"
#include "capd/bitSet/CubFaceIndex.h"
#include "capd/bitSet/CubCellSetFiltrT.hpp"

#include "capd/homologicalAlgebra/FreeChainComplex.hpp"
#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.hpp" // temporarily here, should be compiled into the library
//#include "capd/repSet/ECell3dCode.h"
#include "capd/repSet/ECellMDCodeT.h"

/* Commented out temporarily - needs to be adapted (still the version from CrHomology
void CrbHom(int embDim, const int dims[], const char* bytes, int* betti,int streaming){
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
  CRef<HomologySignature<int> > homSignCR=CubSetFunctors<BCubSet,BCubCelSet>::HomologyViaRepSetReductions(cubSetCR);
  for(int i=0;i<embeddingDim;++i) betti[i]=homSignCR().bettiNumber(i);
}
*/

// Note: only one of the two following methods may be uncommented

// This method kept only for testing purposes for the above version of CrbHom
/* // -------------- keep it here ------------
void CrbHom(const char* fileName){
  int d[3];
  const int* dims=d;
  const char* bitmap=0;
  int betti[3];
  // The CR reference is stored in cubSetCR to avoid premature destroying of the bitmap
  CRef<BCubSet> cubSetCR=readCubFile(fileName,dims,bitmap);
  CrbHom(embeddingDim,dims,bitmap,betti,false);
  for(int i=0;i<embeddingDim;++i) std::cout << "Betti[" << i << "]=" << betti[i]  << std::endl;
}
*/ // -------------- keep it here ------------


typedef ECellMDCodeT<cluster,embeddingDim> CubFaceIndexType;
typedef ECellMDCodeT<cluster,embeddingDim> ElementaryCellType;

/*
typedef ECell3dCode CubFaceIndexType;
typedef ECell3dCode ElementaryCellType;
*/

/*
Obsolete:
typedef CubFaceIndex CubFaceIndexType;
typedef ElementaryCell ElementaryCellType;
*/

typedef CubCellSetT<EuclBitSet,ReductionPairT<CubFaceIndexType> > SCubCelSet;
typedef capd::vectalg::Matrix<int,0,0> MatrixType;
typedef MatrixType::ColumnVectorType ColumnVectorType;
typedef MatrixType::ScalarType ScalarType;
typedef FreeModule<ElementaryCellType,MatrixType> FreeModuleType;
typedef FreeChainComplex<FreeModule<ElementaryCellType,MatrixType> > FreeChainComplexType;
typedef ChainT<std::map<ElementaryCellType,int> > ChainType;


//template FreeChainComplex<FreeModule<ElementaryCell,Matrix<int,0,0> > >::FreeChainComplex<FreeModule<ElementaryCell,Matrix<int,0,0> > >(const std::set<ElementaryCell>&);
//template class FreeChainComplex<FreeModule<CubFaceIndex,Matrix<int,0,0> > >;

void CrbHom(const char* fileName){

  CRef<SCubCelSet> cubCellSetCR=readCubCellSet<BCubSet,SCubCelSet>(fileName);
  Stopwatch swTot;
  CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> homFiltr(cubCellSetCR);
  std::cout << "Computed homology is: \n\n" << homFiltr  << std::endl;
  fcout << "Computation completed in " << swTot  << std::endl;
}
/// @}

