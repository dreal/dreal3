/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ArHomMD.hpp
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
#include <vector>
#include <new>
using namespace std;

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/homologicalAlgebra/RepCubSetBuilder.hpp"
#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"

extern ofstreamcout fcout;

#include "capd/vectalg/MatrixSlice.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"

/*
using namespace capd;
using namespace matrixAlgorithms;
*/

#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubFile.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"

#include "capd/homologicalAlgebra/RepCubSetBuilder.hpp"
#include "capd/repSet/RepSet.h"
#include "capd/repSet/ElementaryCube.h"
#include "capd/homologicalAlgebra/readCubicalSet.hpp"

template<typename P_ElementarySet>
class VectBuilder : public std::vector<P_ElementarySet>{
public:
  typedef P_ElementarySet ElementarySetType;
  VectBuilder<P_ElementarySet>& insert(const ElementarySetType& eset){
    this->push_back(eset);
    return *this;
  }
  const std::vector<P_ElementarySet>& getVector() const{
    return *this;
  }
};

typedef ElementaryCube ElementarySetType;
typedef VectBuilder<ElementarySetType> RepSetType;
typedef FreeModule<int,capd::vectalg::Matrix<int,0,0> > ZFreeModule;
typedef ReducibleFreeChainComplex<ZFreeModule,int> ZRFCComplex;


void ArHomMD(const char* fileName){

  CRef<RepSetType> repSetCR(new RepSetType());
  std::ifstream in;
  in.open(fileName,ios::in);
  RepCubSetBuilder<RepSetType> csb(repSetCR);
  readCubicalSet(in,csb);

  Stopwatch swTot;
  CRef<ZRFCComplex> rfccCR( new ZRFCComplex(repSetCR().getVector()));
  CRef<HomologySignature<int> > homSignCR=HomAlgFunctors<ZFreeModule>::homSignViaAR_Random(rfccCR);
  fcout << "Computed homology is: \n\n" << homSignCR()  << std::endl;
  fcout << "Computation completed in " << swTot  << std::endl;
}
/// @}

