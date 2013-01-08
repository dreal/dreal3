/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file MultiEngHomT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_MULTI_ENG_HOM_T_H_)
#define _MULTI_ENG_HOM_T_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <new>
using namespace std;

#include "capd/vectalg/MatrixSlice.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"
#include "capd/auxil/stringOstream.h"

//-- ofstreamcout fcout;
extern ofstreamcout fcout;

#include "capd/multiEngHom/chomInterface.h"
#include "capd/multiEngHom/homologyInterface.h"
#include "capd/multiEngHom/hombinInterface.h"

using namespace capd;
using namespace matrixAlgorithms;
using namespace std;


#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubFile.hpp"
#include "capd/homologicalAlgebra/acyclicConfigs.hpp"
#include "capd/bitSet/EmbDimException.h"

template <int dim>
struct MultiEngineHomology{
  typedef CubSetT<EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,dim> > BCubSet;
  typedef CubCellSetT<EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,dim> > BCubCelSet;
  typedef CRef<BCubSet> BCubSetCR;
  typedef CubSetFunctors<BCubSet,BCubCelSet> CubSetFunct;
  typedef CRef<HomologySignature<int> > (*HomologyCubAlgorithm)(CRef<BCubSet>);
  typedef CRef<HomologySignature<int> > (*HomologyCelAlgorithm)(CRef<BCubCelSet>);

  typedef std::string (*HomologyInclusionAlgorithm)(CRef<BCubSet>,CRef<BCubSet>);

  static MultiEngineHomology selector;

  std::map<std::string,HomologyCubAlgorithm> homologyCubAlgorithms;
  std::map<std::string,HomologyCelAlgorithm> homologyCelAlgorithms;
  std::map<std::string,HomologyCubAlgorithm> homologyInclusionAlgorithms;

  HomologyCubAlgorithm setupHomologyAlgorithm(const std::string& A_engine){
    HomologyCubAlgorithm selectedAlgorithm;
    if(homologyCubAlgorithms.count(A_engine)) selectedAlgorithm=homologyCubAlgorithms[A_engine];
    else{
      std::string s;
      s << "Bad engine: " << A_engine << " not known or not supported for this dimension\n";
      throw EmbDimException(s);
    }
    return selectedAlgorithm;
  }

  HomologyCelAlgorithm setupHomologyCelAlgorithm(const std::string& A_engine){
    HomologyCelAlgorithm selectedCelAlgorithm;
    if(homologyCelAlgorithms.count(A_engine)) selectedCelAlgorithm=homologyCelAlgorithms[A_engine];
    else{
      std::string s;
      s << "Bad engine: " << A_engine << " not known or not supported for this dimension\n";
      throw EmbDimException(s);
    }
    return selectedCelAlgorithm;
  }

  HomologyInclusionAlgorithm setupHomologyInclusionAlgorithm(const std::string& A_engine){
    HomologyInclusionAlgorithm selectedInclusionAlgorithm;
    if(homologyInclusionAlgorithms.count(A_engine)) selectedInclusionAlgorithm=homologyInclusionAlgorithms[A_engine];
    else{
      std::string s;
      s << "Bad engine: " << A_engine << " not known or not supported for this dimension\n";
      throw EmbDimException(s);
    }
    return selectedInclusionAlgorithm;
  }

  void showResults(const CRef<HomologySignature<int> >& A_hsCR,const std::string& A_engine, int A_verbose){
    fcout.turnOn();
    fcout << std::endl;
    switch(A_verbose){
      case 0: for(unsigned int i=0;i<=A_hsCR().size();++i) fcout << A_hsCR().bettiNumber(i) << " "; break;
      case 1: for(unsigned int i=0;i<=A_hsCR().size();++i){
                fcout << "Betti[" << i << "]=" << A_hsCR().bettiNumber(i) << std::endl;
              }
              break;
      default: fcout << A_hsCR();
    }
    fcout << std::endl;
  }
  // This method runs the particular homology engine for the cubical set in the prescribed file
  // in the prescribed dimension given as the dim template parameter
  void operator()(const char* A_fileName, const std::string& A_engine, int A_verbose){
    if(A_verbose>=3) fcout.turnOn();
    else fcout.turnOff();

    HomologyCubAlgorithm selectedAlgorithm=setupHomologyAlgorithm(A_engine);
    CRef<BCubSet> cubSetCR;
    try{
      cubSetCR=readCubFile<BCubSet,BCubCelSet>(A_fileName);
    }catch(EmbDimException){
      throw EmbDimException("Incorrect embDim");
    }
    if(cubSetCR().embDim()!=dim) throw EmbDimException("Incorrect embDim");
    Stopwatch swTot;
    CRef<HomologySignature<int> > hsCR=selectedAlgorithm(cubSetCR);
    hsCR().shrink();
    showResults(hsCR,A_engine,A_verbose);
    if(A_verbose) fcout << "Computation completed in " << swTot << " under " << A_engine << " engine." << std::endl;
  }

  void operator()(int embDim, const int dims[], const char* bytes, int* betti, const std::string& A_engine="MM_CR", int A_verbose=0){
    if(A_verbose>=3) fcout.turnOn();
    else fcout.turnOff();

    HomologyCubAlgorithm selectedAlgorithm=setupHomologyAlgorithm(A_engine);
    Stopwatch swTot;
    CRef<BCubSet> cubSetCR(new BCubSet(dims,bytes));
    CRef<HomologySignature<int> > hsCR=selectedAlgorithm(cubSetCR);
    hsCR().shrink();
    for(int i=0;i<embDim;++i) betti[i]=hsCR().bettiNumber(i);
    if(A_verbose) fcout << "Computation completed in " << swTot << " under " << A_engine << " engine." << std::endl;
  }

  // This method runs the particular homology engine for the homology inclusion maps
  // of the cubical sets in the prescribed files
  // in the prescribed dimension given as the dim template parameter
  //-- Does not compile yet
/*
  void operator()(const char* A_subFileName, const char* A_supFileName, const std::string& A_engine, int A_verbose){
    if(A_verbose>=3) fcout.turnOn();
    else fcout.turnOff();

    HomologyInclusionAlgorithm selectedInclusionAlgorithm=setupHomologyInclusionAlgorithm(A_engine);
    Stopwatch swTot;
    CRef<BCubSet> subCubSetCR;
    CRef<BCubSet> supCubSetCR;
    try{
      subCubSetCR=readCubFile<BCubSet,BCubCelSet>(A_subFileName);
      supCubSetCR=readCubFile<BCubSet,BCubCelSet>(A_supFileName);
    }catch(EmbDimException){
      throw EmbDimException("Incorrect embDim");
    }
    if(cubSetCR().embDim()!=dim) throw EmbDimException("Incorrect embDim");
    CRef<BCubCelSet> subCubCelSetCR;
    CRef<BCubCelSet> supCubCelSetCR;
    std::string result=selectedInclusionAlgorithm(subCubCelSetCR,supCubCelSetCR);
    fcout << result;
    if(A_verbose) fcout << "Computation completed in " << swTot << " under " << A_engine << " engine." << std::endl;
  }
*/

}; // MultiEngineHomology<dim>

template<int dim>
MultiEngineHomology<dim> MultiEngineHomology<dim>::selector;

template <>
struct MultiEngineHomology<0>{
  MultiEngineHomology<2>& ch2;
  MultiEngineHomology<3>& ch3;
  MultiEngineHomology<4>& ch4;
  MultiEngineHomology<5>& ch5;
  MultiEngineHomology<6>& ch6;
  MultiEngineHomology<7>& ch7;
  MultiEngineHomology<8>& ch8;

/*
  typedef MultiEngineHomology<2>::HomologyInclusionAlgorithm HomologyInclusionAlgorithm2;
  typedef MultiEngineHomology<3>::HomologyInclusionAlgorithm HomologyInclusionAlgorithm3;
  typedef MultiEngineHomology<4>::HomologyInclusionAlgorithm HomologyInclusionAlgorithm4;
*/

  MultiEngineHomology():
    ch2(MultiEngineHomology<2>::selector),
    ch3(MultiEngineHomology<3>::selector),
    ch4(MultiEngineHomology<4>::selector),
    ch5(MultiEngineHomology<5>::selector),
    ch6(MultiEngineHomology<6>::selector),
    ch7(MultiEngineHomology<7>::selector),
    ch8(MultiEngineHomology<8>::selector)
  {

    #define SETUP_ALG(type,dim,name,alg)      \
    MultiEngineHomology<dim>::Homology##type##Algorithm alg##type##dim##Ptr=&MultiEngineHomology<dim>::CubSetFunct::alg;  \
    ch##dim.homology##type##Algorithms.insert(std::make_pair(#name,alg##type##dim##Ptr));

    #define SETUP_EXTALG(type,dim,name,alg)      \
    MultiEngineHomology<dim>::Homology##type##Algorithm alg##type##dim##Ptr=alg<MultiEngineHomology<dim>::BCubSet>;     \
    ch##dim.homology##type##Algorithms.insert(std::make_pair(#name,alg##type##dim##Ptr));

    SETUP_ALG(Cub,2,MM_ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(Cub,2,MM_ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(Cub,2,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cub,2,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cub,2,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cub,2,MM_ASLTns,HomologyViaAcyclicSubspaceLTD3)     // LTD3 works also for dim=1 and 2!
    SETUP_ALG(Cub,2,MM_ASLT,HomologyViaAcyclicSubspaceLTD3Shaved) // LTD3 works also for dim=1 and 2!
    SETUP_ALG(Cub,2,MM_ASos,HomologyViaAcyclicSubspaceOSSIShaved)
    SETUP_ALG(Cub,2,MM_ASR,HomologyViaAcyclicSubspaceSIRShaved)
    SETUP_ALG(Cub,2,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cub,2,MM_AR,HomologyViaAlgebraicReductionsRandom)
    SETUP_ALG(Cub,2,MM_ARso,HomologyViaAlgebraicReductionsSorted)
    SETUP_ALG(Cub,2,MM_ARlso,HomologyViaAlgebraicReductionsLocallySorted)
    SETUP_EXTALG(Cub,2,PP,homologyViaHomologyPackage)
    SETUP_EXTALG(Cub,2,PP_AS,homologyViaHombin)
    SETUP_EXTALG(Cub,2,BK_bm,homologyViaChomPackage)
    SETUP_EXTALG(Cub,2,BK,homologyViaChomPackageStreamed)

    SETUP_ALG(Cel,2,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cel,2,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cel,2,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cel,2,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cel,2,MM_CRf,HomSignViaRepSetReductionsFull)
    SETUP_EXTALG(Cel,2,BK_bm,homologyViaChomPackageCel)
    SETUP_EXTALG(Cel,2,BK,homologyViaChomPackageStreamedCel)


    SETUP_ALG(Cub,3,MM_ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(Cub,3,MM_ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(Cub,3,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cub,3,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cub,3,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cub,3,MM_ASos,HomologyViaAcyclicSubspaceOSSIShaved)
    SETUP_ALG(Cub,3,MM_ASR,HomologyViaAcyclicSubspaceSIRShaved)
    SETUP_ALG(Cub,3,MM_ASLTns,HomologyViaAcyclicSubspaceLTD3)
    SETUP_ALG(Cub,3,MM_ASLT,HomologyViaAcyclicSubspaceLTD3Shaved)
    SETUP_ALG(Cub,3,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cub,3,MM_AR,HomologyViaAlgebraicReductionsRandom)
    SETUP_ALG(Cub,3,MM_ARso,HomologyViaAlgebraicReductionsSorted)
    SETUP_ALG(Cub,3,MM_ARlso,HomologyViaAlgebraicReductionsLocallySorted)
    SETUP_EXTALG(Cub,3,PP,homologyViaHomologyPackage)
    SETUP_EXTALG(Cub,3,PP_AS,homologyViaHombin)
    SETUP_EXTALG(Cub,3,BK_bm,homologyViaChomPackage)
    SETUP_EXTALG(Cub,3,BK_LT,homologyViaChomPackageLT)
    SETUP_EXTALG(Cub,3,BK,homologyViaChomPackageStreamed)

    SETUP_ALG(Cel,3,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cel,3,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cel,3,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cel,3,MM_ASLT,HomologyViaAcyclicSubspaceLTD3Shaved)
    SETUP_ALG(Cel,3,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cel,3,MM_CRf,HomSignViaRepSetReductionsFull)
    SETUP_EXTALG(Cel,3,BK_bm,homologyViaChomPackageCel)
    SETUP_EXTALG(Cel,3,BK,homologyViaChomPackageStreamedCel)

    SETUP_ALG(Cub,4,MM_ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(Cub,4,MM_ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(Cub,4,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cub,4,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cub,4,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cub,4,MM_ASos,HomologyViaAcyclicSubspaceOSSIShaved)
    SETUP_ALG(Cub,4,MM_ASR,HomologyViaAcyclicSubspaceSIRShaved)
    SETUP_ALG(Cub,4,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cub,4,MM_AR,HomologyViaAlgebraicReductionsRandom)
    SETUP_ALG(Cub,4,MM_ARso,HomologyViaAlgebraicReductionsSorted)
    SETUP_ALG(Cub,4,MM_ARlso,HomologyViaAlgebraicReductionsLocallySorted)
    SETUP_EXTALG(Cub,4,PP,homologyViaHomologyPackage)
    SETUP_EXTALG(Cub,4,PP_AS,homologyViaHombin)
    SETUP_EXTALG(Cub,4,BK_bm,homologyViaChomPackage)
    SETUP_EXTALG(Cub,4,BK,homologyViaChomPackageStreamed)

    SETUP_ALG(Cel,4,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cel,4,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cel,4,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cel,4,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cel,4,MM_CRf,HomSignViaRepSetReductionsFull)
    SETUP_EXTALG(Cel,4,BK_bm,homologyViaChomPackageCel)
    SETUP_EXTALG(Cel,4,BK,homologyViaChomPackageStreamedCel)

    SETUP_ALG(Cub,5,MM_ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(Cub,5,MM_ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(Cub,5,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cub,5,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cub,5,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cub,5,MM_ASos,HomologyViaAcyclicSubspaceOSSIShaved)
    SETUP_ALG(Cub,5,MM_ASR,HomologyViaAcyclicSubspaceSIRShaved)
    SETUP_ALG(Cub,5,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cub,5,MM_AR,HomologyViaAlgebraicReductionsRandom)
    SETUP_ALG(Cub,5,MM_ARso,HomologyViaAlgebraicReductionsSorted)
    SETUP_ALG(Cub,5,MM_ARlso,HomologyViaAlgebraicReductionsLocallySorted)
    SETUP_EXTALG(Cub,5,PP,homologyViaHomologyPackage)
    SETUP_EXTALG(Cub,5,PP_AS,homologyViaHombin)
    SETUP_EXTALG(Cub,5,BK_bm,homologyViaChomPackage)
    SETUP_EXTALG(Cub,5,BK,homologyViaChomPackageStreamed)

    SETUP_ALG(Cel,5,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cel,5,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cel,5,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cel,5,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cel,5,MM_CRf,HomSignViaRepSetReductionsFull)
    SETUP_EXTALG(Cel,5,BK_bm,homologyViaChomPackageCel)
    SETUP_EXTALG(Cel,5,BK,homologyViaChomPackageStreamedCel)

    SETUP_ALG(Cub,6,MM_ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(Cub,6,MM_ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(Cub,6,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cub,6,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cub,6,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cub,6,MM_ASos,HomologyViaAcyclicSubspaceOSSIShaved)
    SETUP_ALG(Cub,6,MM_ASR,HomologyViaAcyclicSubspaceSIRShaved)
    SETUP_ALG(Cub,6,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cub,6,MM_AR,HomologyViaAlgebraicReductionsRandom)
    SETUP_ALG(Cub,6,MM_ARso,HomologyViaAlgebraicReductionsSorted)
    SETUP_ALG(Cub,6,MM_ARlso,HomologyViaAlgebraicReductionsLocallySorted)
    SETUP_EXTALG(Cub,6,PP,homologyViaHomologyPackage)
    SETUP_EXTALG(Cub,6,PP_AS,homologyViaHombin)
    SETUP_EXTALG(Cub,6,BK_bm,homologyViaChomPackage)
    SETUP_EXTALG(Cub,6,BK,homologyViaChomPackageStreamed)

    SETUP_ALG(Cel,6,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cel,6,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cel,6,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cel,6,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cel,6,MM_CRf,HomSignViaRepSetReductionsFull)
    SETUP_EXTALG(Cel,6,BK_bm,homologyViaChomPackageCel)
    SETUP_EXTALG(Cel,6,BK,homologyViaChomPackageStreamedCel)

    SETUP_ALG(Cub,7,MM_ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(Cub,7,MM_ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(Cub,7,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cub,7,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cub,7,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cub,7,MM_ASos,HomologyViaAcyclicSubspaceOSSIShaved)
    SETUP_ALG(Cub,7,MM_ASR,HomologyViaAcyclicSubspaceSIRShaved)
    SETUP_ALG(Cub,7,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cub,7,MM_AR,HomologyViaAlgebraicReductionsRandom)
    SETUP_ALG(Cub,7,MM_ARso,HomologyViaAlgebraicReductionsSorted)
    SETUP_ALG(Cub,7,MM_ARlso,HomologyViaAlgebraicReductionsLocallySorted)
    SETUP_EXTALG(Cub,7,PP,homologyViaHomologyPackage)
    SETUP_EXTALG(Cub,7,PP_AS,homologyViaHombin)
    SETUP_EXTALG(Cub,7,BK_bm,homologyViaChomPackage)
    SETUP_EXTALG(Cub,7,BK,homologyViaChomPackageStreamed)

    SETUP_ALG(Cel,7,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cel,7,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cel,7,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cel,7,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cel,7,MM_CRf,HomSignViaRepSetReductionsFull)
    SETUP_EXTALG(Cel,7,BK_bm,homologyViaChomPackageCel)
    SETUP_EXTALG(Cel,7,BK,homologyViaChomPackageStreamedCel)

    SETUP_ALG(Cub,8,MM_ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(Cub,8,MM_ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(Cub,8,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cub,8,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cub,8,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cub,8,MM_ASos,HomologyViaAcyclicSubspaceOSSIShaved)
    SETUP_ALG(Cub,8,MM_ASR,HomologyViaAcyclicSubspaceSIRShaved)
    SETUP_ALG(Cub,8,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cub,8,MM_AR,HomologyViaAlgebraicReductionsRandom)
    SETUP_ALG(Cub,8,MM_ARso,HomologyViaAlgebraicReductionsSorted)
    SETUP_ALG(Cub,8,MM_ARlso,HomologyViaAlgebraicReductionsLocallySorted)
    SETUP_EXTALG(Cub,8,PP,homologyViaHomologyPackage)
    SETUP_EXTALG(Cub,8,PP_AS,homologyViaHombin)
    SETUP_EXTALG(Cub,8,BK_bm,homologyViaChomPackage)
    SETUP_EXTALG(Cub,8,BK,homologyViaChomPackageStreamed)

    SETUP_ALG(Cel,8,MM_ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(Cel,8,MM_AS1C,HomologyViaAcyclicSubspaceSI_1C)
    SETUP_ALG(Cel,8,MM_AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(Cel,8,MM_CR,HomSignViaRepSetReductions)
    SETUP_ALG(Cel,8,MM_CRf,HomSignViaRepSetReductionsFull)
    SETUP_EXTALG(Cel,8,BK_bm,homologyViaChomPackageCel)
    SETUP_EXTALG(Cel,8,BK,homologyViaChomPackageStreamedCel)

    #undef SETUP_ALG
    #undef SETUP_EXTALG

//    ch3.HomologyInclusionAlgorithm3.insert(std::make_pair("MM_CR",CrbIncHom));

  }

  void failure(const std::string& A_engine, int A_verbose){
    if(A_engine=="BK_bm" || A_engine=="BK_LT" || A_engine=="PP_AS" || A_engine=="MM_ASLT" || A_engine=="MM_ASLTns"){
      string s;
      s << "The only dimension accepted for " << A_engine << " is 3\n";
      throw EmbDimException(s);
    }else if(A_engine=="MM_CR" || A_engine=="MM_AR" || A_engine=="MM_ASLT" || A_engine=="PP"){
      string s;
      s << "Dimensions accepted for " << A_engine << " are: 2, 3, and 4\n";
      throw EmbDimException(s);
    }else{
      string s;
      s << "Engine " << A_engine << " is incorrect.\n";
      throw EmbDimException(s);
    }
  }

  // This method runs the particular homology engine for the cubical set in the prescribed file
  // trying various dimensions
  void operator()(const char* A_fileName, const std::string& A_engine, int A_verbose){
    readAcyclicConfigs();
    for(int i=2;i<5;++i){
      try{
        switch(i){
          case 2: ch2(A_fileName,A_engine,A_verbose);
                  return;
          case 3: ch3(A_fileName,A_engine,A_verbose);
                  return;
          case 4: ch4(A_fileName,A_engine,A_verbose);
                  return;
          case 5: ch5(A_fileName,A_engine,A_verbose);
                  return;
          case 6: ch6(A_fileName,A_engine,A_verbose);
                  return;
          case 7: ch7(A_fileName,A_engine,A_verbose);
                  return;
          case 8: ch8(A_fileName,A_engine,A_verbose);
                  return;
        }
      }catch(EmbDimException& e){
//        std::string w(e.what());
//        if(w != std::string("Incorrect embDim") && w.substr(0,14) != std::string("Got file type ")) throw;
      };
    }
    failure(A_engine, A_verbose);
  }

  // This method runs the particular homology engine for the cubical set in the provided bitmap
  // trying various dimensions
  void operator()(int embDim, const int dims[], const char* bytes, int* betti, const std::string& A_engine="MM_CR", int A_verbose=1){
    readAcyclicConfigs();
    if(dims[0] % 32) throw std::runtime_error("The 0th dimension must be a multiciplity of 32!");
    CRef<BCubSet> cubSetCR(new BCubSet(dims,bytes));
    switch(embDim){
      case 2: ch2(2,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 3: ch3(3,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 4: ch4(4,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 5: ch5(5,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 6: ch6(6,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 7: ch7(7,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 8: ch8(8,dims,bytes,betti,A_engine,A_verbose);
              return;
    }
  }

};// MultiEngineHomology<0>

#endif //_MULTI_ENG_HOM_T_H_
/// @}

