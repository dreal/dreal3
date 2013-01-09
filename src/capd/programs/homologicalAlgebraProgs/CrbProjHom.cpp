/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrbProjHom.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*
     This program computes the matrix of the homlogy map of
     a projection from the domain to the range space provided on input
*/

#include <iostream>
#include <cstdlib>

#include "capd/auxil/ofstreamcout.h"
ofstreamcout fcout;

#include "capd/auxil/handleUnexpectedTerminate.h"
#include "capd/homologicalAlgebra/ChainMapCrHom.hpp"
#include "capd/homologicalAlgebra/ProjChainMap.hpp"

// Embedding dimensions for this executable

const int domEmbDim=3;
const int rngEmbDim=2;

typedef int ScalarType;
typedef unsigned long int cluster;
typedef ECellMDCodeT<cluster,domEmbDim> DomGenType;
typedef ECellMDCodeT<cluster,rngEmbDim> RngGenType;
typedef BitSetT<BitmapT<cluster> > BitSet;
typedef EuclBitSetT<BitSet,domEmbDim> DomEuclBitSet;
typedef EuclBitSetT<BitSet,rngEmbDim> RngEuclBitSet;
typedef CubSetT<DomEuclBitSet> DomBCubSet;
typedef CubSetT<RngEuclBitSet> RngBCubSet;
typedef CubCellSetT<DomEuclBitSet,ReductionPairT<DomGenType> > DomSCubCelSet;
typedef CubCellSetT<RngEuclBitSet,ReductionPairT<RngGenType> > RngSCubCelSet;
typedef capd::vectalg::Matrix<ScalarType,0,0> MatrixType;
typedef FreeModule<DomGenType,MatrixType> DomFreeModuleType;
typedef FreeChainComplex<DomFreeModuleType> DomFreeChainComplexType;
typedef FreeModule<RngGenType,MatrixType> RngFreeModuleType;
typedef FreeChainComplex<RngFreeModuleType> RngFreeChainComplexType;

typedef ChainT<std::map<DomGenType,ScalarType> > DomChainType;
typedef ChainT<std::map<RngGenType,ScalarType> > RngChainType;

typedef ProjChainMap<DomChainType,RngChainType> ProjChainMapType;

RngGenType projMap(DomGenType domGen){
  return RngGenType(domGen);
}

std::string CrbProjHom(const char* domFileName,const char* rngFileName){

  CRef<DomSCubCelSet> domCubCellSetCR=readCubCellSet<DomBCubSet,DomSCubCelSet>(domFileName);
  CRef<RngSCubCelSet> rngCubCellSetCR=readCubCellSet<RngBCubSet,RngSCubCelSet>(rngFileName);

  ProjChainMapType projChainMap(projMap);
  ChainMapCrHom<DomSCubCelSet,RngSCubCelSet,ScalarType,ProjChainMapType> cmh(projChainMap);
  return cmh.getHomMatrix(domCubCellSetCR,rngCubCellSetCR);
}

int main(int argc,char **argv){
  set_unexpected(handle_unexpected);
  set_terminate(handle_terminate);

  fcout.open("out.txt");
  fcout.turnOn();

  // Check arguments
/*
  if (argc < 2) {
    std::ostringstream s;
    s << "!Usage " << argv[0] << " domfilename rngfilename " << std::endl;
    throw std::runtime_error(s.str());
  }
*/

  try{
//    std::string s=CrbProjHom(argv[1],argv[2]);
    std::string s=CrbProjHom("T.cub","ring.cub");
//    std::string s=CrbProjHom("S1xYZ.txt","bar.txt");
//    std::string s=CrbProjHom("S1.txt","S1.txt");
//    std::string s=CrbProjHom("bar.txt","bar.txt");
    fcout << s << std::endl;
  }catch(std::exception& e){
    fcout << "Caught exception: " << e.what() << endl;
  }catch(std::string& s){
    fcout << "Caught exception: " << s.c_str() << endl;
  }catch(const char* c){
    fcout << "Caught exception: " << c << endl;
  }catch(...){
    fcout << "Caught an unknown exception: " << endl;
  }
}

/// @}

