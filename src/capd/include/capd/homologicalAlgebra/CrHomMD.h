/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrHomMD.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2007
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_CR_HOM_T_H_)
#define _CR_HOM_T_H_

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

using namespace capd;
using namespace matrixAlgorithms;
using namespace std;


#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubCellSet.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
#include "capd/bitSet/EmbDimException.h"

template <int dim>
struct CrHom{
  typedef CubSetT<EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,dim> > BCubSet;
  typedef CubCellSetT<EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,dim> > BCubCelSet;
  typedef CRef<BCubCelSet> BCubSetCR;
  typedef CubSetFunctors<BCubSet,BCubCelSet> CubSetFunct;
  typedef CRef<HomologySignature<int> > (*HomologyAlgorithm)(CRef<BCubCelSet>);

  static CrHom selector;

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
    if(A_verbose) fcout << "CrHomMD 0.9 (c) Marian Mrozek, 2007" << std::endl;
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

    CRef<BCubCelSet> cubCellSetCR;
    try{
      cubCellSetCR=readCubCellSet<BCubSet,BCubCelSet>(A_fileName);
    }catch(EmbDimException){
      throw EmbDimException("Incorrect embDim");
    }
    if(cubCellSetCR().embDim()!=dim) throw EmbDimException("Incorrect embDim");

    HomologyAlgorithm selectedAlgorithm=setupHomologyAlgorithm(A_engine);
    Stopwatch swTot;
    CRef<HomologySignature<int> > hsCR=selectedAlgorithm(cubCellSetCR);
    hsCR().shrink();
    showResults(hsCR,A_engine,A_verbose);
    if(A_verbose) fcout << "CR homology algorithm finished in " << swTot << std::endl;
  }

  void operator()(int embDim, const int dims[], const char* bytes, int* betti, const std::string& A_engine="CR", int A_verbose=0){
    if(A_verbose>=3) fcout.turnOn();
    else fcout.turnOff();

    HomologyAlgorithm selectedAlgorithm=setupHomologyAlgorithm(A_engine);
    Stopwatch swTot;
    CRef<BCubCelSet> cubCellSetCR(new BCubCelSet(dims,bytes));
    CRef<HomologySignature<int> > hsCR=selectedAlgorithm(cubCellSetCR);
    hsCR().shrink();
    for(int i=0;i<embDim;++i) betti[i]=hsCR().bettiNumber(i);
    if(A_verbose) fcout << "CR homology algorithm finished in " << swTot << std::endl;
  }

}; // CrHom<dim>

template<int dim>
CrHom<dim> CrHom<dim>::selector;

template <>
struct CrHom<0>{
  CrHom<2>& ch2;
  CrHom<3>& ch3;
  CrHom<4>& ch4;
  CrHom<5>& ch5;
  CrHom<6>& ch6;
  CrHom<7>& ch7;
  CrHom<8>& ch8;
  CrHom<9>& ch9;
  CrHom<10>& ch10;
  CrHom<11>& ch11;
  CrHom<12>& ch12;

  CrHom():
    ch2(CrHom<2>::selector),
    ch3(CrHom<3>::selector),
    ch4(CrHom<4>::selector),
    ch5(CrHom<5>::selector),
    ch6(CrHom<6>::selector),
    ch7(CrHom<7>::selector),
    ch8(CrHom<8>::selector),
    ch9(CrHom<9>::selector),
    ch10(CrHom<10>::selector),
    ch11(CrHom<11>::selector),
    ch12(CrHom<12>::selector)
  {
    #define SETUP_ALG(dim,name,alg)      \
    CrHom<dim>::HomologyAlgorithm alg##dim##Ptr=&CrHom<dim>::CubSetFunct::alg;  \
    ch##dim.homologyAlgorithms.insert(std::make_pair(#name,alg##dim##Ptr));

    SETUP_ALG(2,CR,HomSignViaRepSetReductions)
    SETUP_ALG(3,CR,HomSignViaRepSetReductions)
    SETUP_ALG(4,CR,HomSignViaRepSetReductions)
    SETUP_ALG(5,CR,HomSignViaRepSetReductions)
    SETUP_ALG(6,CR,HomSignViaRepSetReductions)
    SETUP_ALG(7,CR,HomSignViaRepSetReductions)
    SETUP_ALG(8,CR,HomSignViaRepSetReductions)
    SETUP_ALG(9,CR,HomSignViaRepSetReductions)
    SETUP_ALG(10,CR,HomSignViaRepSetReductions)
    SETUP_ALG(11,CR,HomSignViaRepSetReductions)
    SETUP_ALG(12,CR,HomSignViaRepSetReductions)

    #undef SETUP_ALG
  }

  void failure(const std::string& A_engine, int A_verbose){
    string s;
    s << A_engine << " is incorrect or not available for this dimension.\n";
    throw EmbDimException(s);
  }

  // This method runs the particular homology engine for the cubical set in the prescribed file
  // trying various dimensions
  void operator()(const char* A_fileName, const std::string& A_engine, int A_verbose){
    for(int i=2;i<=12;++i){
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
          case 9: ch9(A_fileName,A_engine,A_verbose);
                  return;
          case 10: ch10(A_fileName,A_engine,A_verbose);
                  return;
          case 11: ch11(A_fileName,A_engine,A_verbose);
                  return;
          case 12: ch12(A_fileName,A_engine,A_verbose);
                  return;
          default:;
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
    CRef<BCubCelSet> cubCellSetCR(new BCubCelSet(dims,bytes));
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
      case 9: ch9(9,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 10: ch10(10,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 11: ch11(11,dims,bytes,betti,A_engine,A_verbose);
              return;
      case 12: ch12(12,dims,bytes,betti,A_engine,A_verbose);
              return;
      default:;
    }
  }

};// CrHom<0>

#endif //_CR_HOM_T_H_
/// @}

