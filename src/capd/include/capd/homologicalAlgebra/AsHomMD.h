/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file AsHomMD.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_AS_HOM_T_H_)
#define _AS_HOM_T_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <new>
using namespace std;

#include "capd/vectalg/MatrixSlice.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"
#include "capd/auxil/stringOstream.h"

//ofstreamcout fcout;

using namespace capd;
using namespace matrixAlgorithms;
using namespace std;


#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubFile.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
#include "capd/homologicalAlgebra/acyclicConfigs.hpp"
#include "capd/bitSet/EmbDimException.h"

template <int dim>
struct AsHom{
  typedef CubSetT<EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,dim> > BCubSet;
  typedef CubCellSetT<EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,dim> > BCubCelSet;
  typedef CRef<BCubSet> BCubSetCR;
  typedef CubSetFunctors<BCubSet,BCubCelSet> CubSetFunct;
  typedef CRef<HomologySignature<int> > (*HomologyAlgorithm)(CRef<BCubSet>);

  static AsHom selector;

  std::map<std::string,HomologyAlgorithm> homologyAlgorithms;

  HomologyAlgorithm setupHomologyAlgorithm(const std::string& A_engine){
    HomologyAlgorithm selectedAlgorithm;
    if(homologyAlgorithms.count(A_engine)) selectedAlgorithm=homologyAlgorithms[A_engine];
    else{
      std::string s;
      s << "Bad engine: " << A_engine << " not known or not supported for this dimension\n";
      throw EmbDimException(s);
    }
    return selectedAlgorithm;
  }

  void showResults(const CRef<HomologySignature<int> >& A_hsCR,const std::string& A_engine, int A_verbose){
    fcout.turnOn();
    if(A_verbose) fcout << "AsHomMD 0.9 (c) Marian Mrozek, 2006" << std::endl;
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

    CRef<BCubSet> cubSetCR;
    try{
      cubSetCR=readCubFile<BCubSet,BCubCelSet>(A_fileName);
    }catch(EmbDimException){
      throw EmbDimException("Incorrect embDim");
    }
    if(cubSetCR().embDim()!=dim) throw EmbDimException("Incorrect embDim");

    HomologyAlgorithm selectedAlgorithm=setupHomologyAlgorithm(A_engine);
    Stopwatch swTot;
    CRef<HomologySignature<int> > hsCR=selectedAlgorithm(cubSetCR);
    hsCR().shrink();
    showResults(hsCR,A_engine,A_verbose);
    if(A_verbose) fcout << "Computation completed in " << swTot << " under " << A_engine << " engine." << std::endl;
  }

  void operator()(int embDim, const int dims[], const char* bytes, int* betti, const std::string& A_engine="CR", int A_verbose=0){
    if(A_verbose>=3) fcout.turnOn();
    else fcout.turnOff();

    HomologyAlgorithm selectedAlgorithm=setupHomologyAlgorithm(A_engine);
    Stopwatch swTot;
    CRef<BCubSet> cubSetCR(new BCubSet(dims,bytes));
    CRef<HomologySignature<int> > hsCR=selectedAlgorithm(cubSetCR);
    hsCR().shrink();
    for(int i=0;i<embDim;++i) betti[i]=hsCR().bettiNumber(i);
    if(A_verbose) fcout << "Computation completed in " << swTot << " under " << A_engine << " engine." << std::endl;
  }

}; // AsHom<dim>

template<int dim>
AsHom<dim> AsHom<dim>::selector;



template <>
struct AsHom<0>{
  AsHom<2>& ch2;
  AsHom<3>& ch3;
  AsHom<4>& ch4;
  AsHom<5>& ch5;
  AsHom<6>& ch6;
  AsHom<7>& ch7;
  AsHom<8>& ch8;

  AsHom():
    ch2(AsHom<2>::selector),
    ch3(AsHom<3>::selector),
    ch4(AsHom<4>::selector),
    ch5(AsHom<5>::selector),
    ch6(AsHom<6>::selector),
    ch7(AsHom<7>::selector),
    ch8(AsHom<8>::selector)
  {
    #define SETUP_ALG(dim,name,alg)      \
    AsHom<dim>::HomologyAlgorithm alg##dim##Ptr=&AsHom<dim>::CubSetFunct::alg;  \
    ch##dim.homologyAlgorithms.insert(std::make_pair(#name,alg##dim##Ptr));

    SETUP_ALG(2,ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(2,ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(2,ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(2,AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(2,ASRns,HomologyViaAcyclicSubspaceSIR)
    SETUP_ALG(2,ASR,HomologyViaAcyclicSubspaceSIRShaved)

    SETUP_ALG(3,ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(3,ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(3,ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(3,AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(3,ASRns,HomologyViaAcyclicSubspaceSIR)
    SETUP_ALG(3,ASR,HomologyViaAcyclicSubspaceSIRShaved)
    SETUP_ALG(3,ASLTns,HomologyViaAcyclicSubspaceLTD3)
    SETUP_ALG(3,ASLT,HomologyViaAcyclicSubspaceLTD3Shaved)

    SETUP_ALG(4,ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(4,ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(4,ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(4,AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(4,ASRns,HomologyViaAcyclicSubspaceSIR)
    SETUP_ALG(4,ASR,HomologyViaAcyclicSubspaceSIRShaved)

    SETUP_ALG(5,ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(5,ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(5,ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(5,AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(5,ASRns,HomologyViaAcyclicSubspaceSIR)
    SETUP_ALG(5,ASR,HomologyViaAcyclicSubspaceSIRShaved)

    SETUP_ALG(6,ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(6,ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(6,ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(6,AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(6,ASRns,HomologyViaAcyclicSubspaceSIR)
    SETUP_ALG(6,ASR,HomologyViaAcyclicSubspaceSIRShaved)

    SETUP_ALG(7,ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(7,ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(7,ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(7,AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(7,ASRns,HomologyViaAcyclicSubspaceSIR)
    SETUP_ALG(7,ASR,HomologyViaAcyclicSubspaceSIRShaved)

    SETUP_ALG(8,ASHns,HomologyViaAcyclicSubspaceHOM)
    SETUP_ALG(8,ASH,HomologyViaAcyclicSubspaceHOMShaved)
    SETUP_ALG(8,ASns,HomologyViaAcyclicSubspaceSI)
    SETUP_ALG(8,AS,HomologyViaAcyclicSubspaceSIShaved)
    SETUP_ALG(8,ASRns,HomologyViaAcyclicSubspaceSIR)
    SETUP_ALG(8,ASR,HomologyViaAcyclicSubspaceSIRShaved)

    #undef SETUP_ALG
  }

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

  // This method runs the particular homology engine for the cubical set in the prescribed file
  // trying various dimensions
  void operator()(const char* A_fileName, const std::string& A_engine, int A_verbose){
    readAcyclicConfigs();
    for(int i=2;i<=8;++i){
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
        if(e.what() != std::string("Incorrect embDim")) throw;
      };
    }
    failure(A_engine, A_verbose);
  }

  // This method runs the particular homology engine for the cubical set in the provided bitmap
  // trying various dimensions
  void operator()(int embDim, const int dims[], const char* bytes, int* betti, const std::string& A_engine="CR", int A_verbose=1){
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
      case 5: ch4(5,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 6: ch4(6,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 7: ch4(7,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 8: ch4(8,dims,bytes,betti,A_engine,A_verbose);
              return;
    }
  }

};// AsHom<0>

#endif //_AS_HOM_T_H_
/// @}

