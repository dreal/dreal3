/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file RedHom.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_REDHOM_HPP_)
#define _REDHOM_HPP_
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
#include "capd/auxil/CRef.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/stringOstream.h"

extern ofstreamcout fcout;

#include "capd/vectalg/MatrixSlice.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"


#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubFile.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"

#include "capd/homologicalAlgebra/RepCubSetBuilder.hpp"
#include "capd/repSet/RepSet.h"
#include "capd/repSet/ElementaryCube.h"
#include "capd/repSet/ECellMDCodeT.h"
#include "capd/homologicalAlgebra/readCubicalSet.hpp"
#include "capd/homologicalAlgebra/CubSetBuilder.h"

#include "capd/homologicalAlgebra/CubSetBuilder.h"
#include "capd/homologicalAlgebra/BmpCubSetBuilder.hpp"
#include "capd/homologicalAlgebra/BmpCubCelSetBuilder.hpp"
#include "capd/homologicalAlgebra/readCubicalSet.hpp"
#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.hpp"
#include "capd/vectalg/Zp.h"
#include "capd/homologicalAlgebra/acyclicConfigs.hpp"

template<int dim>
void getHomology(const char* fileName,FileType fileType,bool fullCubes,const std::string& engine){
  typedef unsigned long int cluster;
  typedef CubSetT<EuclBitSetT<BitSetT<BitmapT<cluster> >,dim> > CubSet;
  typedef CubCellSetT<EuclBitSetT<BitSetT<BitmapT<cluster> >,dim> > CubCelSet;
  typedef CRef<CubSet> CubSetCR;
  typedef CRef<CubCelSet> CubCelSetCR;
  typedef CubSetFunctors<CubSet,CubCelSet> CubSetFunct;

//  typedef int ScalarType;
//  typedef Zp<3> ScalarType;
  typedef Zp ScalarType;
  typedef HomologySignature<ScalarType> HomologySignatureType;
  typedef CRef<HomologySignatureType> (*HomologyAlgorithm)(CRef<CubCelSet>);
  typedef ECellMDCodeT<cluster,dim> ElementaryCellType;
  typedef capd::vectalg::Matrix<ScalarType,0,0> MatrixType;
  typedef FreeModule<ElementaryCellType,MatrixType> FreeModuleType;
  typedef FreeChainComplex<FreeModule<ElementaryCellType,MatrixType> > FreeChainComplexType;
  typedef CubSetFunctors<CubSet,CubCelSet,FreeChainComplexType> CubSetFunctorsType;

  Stopwatch swRead;
  CubCelSetCR cubCelSetCR(new CubCelSet);
  CubSetCR cubSetCR(new CubSet);

  switch(fileType){
    case bin:{
      if(fullCubes){
        CubSet cubSet;
        cubSet.readBmp(fileName);
        if((dim==2 || dim==3) && engine=="AS"){
          swap(cubSet,cubSetCR());
        }else{
          CubCelSet cubCelSet(cubSet);
          swap(cubCelSet,cubCelSetCR());
        }
      }else{
        CubCelSet cubCelSet;
        cubCelSet.readBmp(fileName);
        swap(cubCelSet,cubCelSetCR());
      }
    }
    break;
    case plain:
    case setOfFullCubes:
    case setOfCubes:{
      if(fullCubes){
        std::ifstream in;
        in.open(fileName,ios::in);
        BmpCubSetBuilder<CubSet> csb(cubSetCR);
        readCubicalSet(in,csb);
        if(dim>3 || engine!="AS"){
          CubCelSet cubCelSet(cubSetCR());
          swap(cubCelSet,cubCelSetCR());
        }
      }else{
        std::ifstream in;
        in.open(fileName,ios::in);
        BmpCubCelSetBuilder<CubCelSet> csb(cubCelSetCR);
        readCubicalSet(in,csb);
      }
    }
    break;
    default:
      throw "Unrecognized file type\n";
  }
  std::cout << "Reading completed in " << swRead  << std::endl;

  Stopwatch swTot;
  CRef<HomologySignatureType> homSignCR;
  if(fullCubes && engine=="AS" && (dim==2 || dim==3)){
    fcout << "Using AS algorithm" << std::endl;
    homSignCR=CubSetFunctorsType::HomologyViaAcyclicSubspaceLTD3ShavedOverField(cubSetCR);
  }else{
    fcout << "Using CR algorithm" << std::endl;
    homSignCR=CubSetFunctorsType::HomSignViaRepSetReductionsOverField(cubCelSetCR);
  }
  std::cout << "Computed homology is: \n\n" << homSignCR()  << std::endl;
  std::cout << "Computation completed in " << swTot  << std::endl;
}




void RedHom(const char* fileName,const std::string& engine){
  std::ifstream in;
  in.open(fileName,ios::in);
  if(!in.good()){
    std::string s;
    s << "Unable to open file " << fileName << " for reading\n";
    throw std::runtime_error(s.c_str());
  }

  CubSetBuilder csb;
  readCubicalSet(in,csb,true); //true means only get dim and type
  in.close();

  unsigned int embDim=csb.getDim();
  FileType fileType=csb.getFileType();
  bool fullCubes=csb.onlyFullCubes();
  #define GETHOM(d) case d:  getHomology<d>(fileName,fileType,fullCubes,engine);break;
  switch(embDim){

    GETHOM(2)
    GETHOM(3)

    GETHOM(4)

    GETHOM(5)
    GETHOM(6)
    GETHOM(7)
    GETHOM(8)
    GETHOM(9)
    GETHOM(10)
    GETHOM(11)
    GETHOM(12)
    GETHOM(13)
    GETHOM(14)

    #undef GETHOM
    default:
      throw "RedHom: unsupported dimension\n";
  }
}
/// @}

#endif //_REDHOM_HPP_
