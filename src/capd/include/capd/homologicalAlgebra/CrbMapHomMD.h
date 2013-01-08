/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrbMapHomMD.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*
     This program computes the matrix of the homlogy map of
     a projection from the domain to the range space provided on input
*/

#if !defined(_CRBMAPHOMMD_H_)
#define _CRBMAPHOMMD_H_

#include <iostream>

#include <cstdlib>
#include <iomanip>

#include "capd/auxil/AdvStopwatch.h"
#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/homologicalAlgebra/readCubicalSet.hpp"
#include "capd/homologicalAlgebra/BmpCubCelSetBuilder.hpp"
#include "capd/homologicalAlgebra/MVCelMapCrHom.hpp"
#include "capd/repSet/ECellMDCodeT.h"



template<int embDim>
struct CrbMapHom{
  static const int domEmbDim=embDim;
  static const int rngEmbDim=embDim;
  static const int graphEmbDim=domEmbDim+rngEmbDim;

  typedef int ScalarType;
  typedef unsigned long int cluster;
  typedef unsigned long long longcluster;
  typedef ECellMDCodeT<longcluster,graphEmbDim> GraphGenType;
  typedef ECellMDCodeT<cluster,domEmbDim> DomGenType;
  typedef ECellMDCodeT<cluster,rngEmbDim> RngGenType;

  typedef BitSetT<BitmapT<cluster> > BitSet;
  typedef EuclBitSetT<BitSet,domEmbDim> DomEuclBitSet;
  typedef EuclBitSetT<BitSet,rngEmbDim> RngEuclBitSet;
  typedef EuclBitSetT<BitSet,graphEmbDim> GraphEuclBitSet;
  typedef CubCellSetT<DomEuclBitSet,ReductionPairT<DomGenType> > DomCubCelSet;
  typedef CubCellSetT<RngEuclBitSet,ReductionPairT<RngGenType> > RngCubCelSet;
  typedef CubCellSetT<GraphEuclBitSet,ReductionPairT<GraphGenType> > GraphCubCelSet;

  typedef BmpCubCelMVMapBuilder<GraphCubCelSet,DomCubCelSet,RngCubCelSet> BmpCubCelMVMapBuilderType;
  typedef MVCelMapCrHom<GraphCubCelSet,DomCubCelSet,RngCubCelSet,ScalarType> MVMapCrHomType;

  static CrbMapHom selector;

  void operator()(const char* A_fileName, bool A_preShave, int A_verbose=3){
    if(A_verbose>=3) fcout.turnOn();
    else fcout.turnOff();

    Stopwatch swTot,swRead;
    AdvStopwatch swTot2;
    std::fstream in;
    in.open(A_fileName,ios::in);

    CRef<GraphCubCelSet> graphCR=CRef<GraphCubCelSet>(new GraphCubCelSet());
    CRef<DomCubCelSet> domCR=CRef<DomCubCelSet>(new DomCubCelSet());
    CRef<RngCubCelSet> rngCR=CRef<RngCubCelSet>(new RngCubCelSet());

    BmpCubCelMVMapBuilderType csb(graphCR,domCR,rngCR);
    readCubicalMap(in,csb);
    std::cout << "Reading completed in " << swRead  << "\n";

    Stopwatch swComp;
    AdvStopwatch swComp2;
    MVMapCrHomType mapCrHom(graphCR,domCR,rngCR,A_preShave);
    swComp2.stop();

    std::string s=mapCrHom.getHomMatrixSignature();
    std::cout << s << std::endl;
    std::cout << "Computation completed in " << swComp2  << "\n";
    std::cout << "Total time (including input/output time) " << swTot  << "\n";
  }
};

template<int dim>
CrbMapHom<dim> CrbMapHom<dim>::selector;

template <>
struct CrbMapHom<0>{
  CrbMapHom<2>& ch2;
  CrbMapHom<3>& ch3;
  CrbMapHom<4>& ch4;
  CrbMapHom<5>& ch5;
  CrbMapHom<6>& ch6;

  CrbMapHom():
    ch2(CrbMapHom<2>::selector),
    ch3(CrbMapHom<3>::selector),
    ch4(CrbMapHom<4>::selector),
    ch5(CrbMapHom<5>::selector),
    ch6(CrbMapHom<6>::selector)

  {}
/*
  void failure(const std::string& A_engine, int A_verbose){
    if(A_engine=="ASLT" || A_engine=="ASLTns"){
      string s;
      s << "The only dimension accepted for " << A_engine << " is 3\n";
      throw EmbDimException(s);
    }else{
      string s;
      s << A_engine << " is incorrect or not available for this dimension.\n";
      throw EmbDimException(s);
    }
  }
*/

  void operator()(const char* A_fileName, bool A_preShave, int A_verbose=3){
    for(int i=2;i<=6;++i){
      try{
        switch(i){
          case 2: ch2(A_fileName,A_preShave,A_verbose);
                  return;
          case 3: ch3(A_fileName,A_preShave,A_verbose);
                  return;
          case 4: ch4(A_fileName,A_preShave,A_verbose);
                  return;
          case 5: ch5(A_fileName,A_preShave,A_verbose);
                  return;
          case 6: ch6(A_fileName,A_preShave,A_verbose);
                  return;
        }
      }catch(EmbDimException& e){
//        if(e.what() != std::string("Incorrect embDim")) throw;
      };
    }
    throw EmbDimException("The only accepted embedding dims are 2,3,4,5,6!");
//    failure(A_engine, A_verbose);
  }
};


#endif //_CRBMAPHOMMD_H_



/// @}

