/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file toCub.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_TOCUB_HPP_)
#define _TOCUB_HPP_
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

//#include "capd/homologicalAlgebra/readCubFile.hpp"

//#include "capd/homologicalAlgebra/RepCubSetBuilder.hpp"

#include "capd/homologicalAlgebra/CubSetBuilder.h"
#include "capd/homologicalAlgebra/BmpCubSetBuilder.hpp"
#include "capd/homologicalAlgebra/BmpCubCelSetBuilder.hpp"
#include "capd/homologicalAlgebra/readCubicalSet.hpp"

template<int dim>
void convert(const char* inFileName,const char* outFileName,FileType fileType,bool fullCubes){
  typedef unsigned long int cluster;
  typedef CubSetT<EuclBitSetT<BitSetT<BitmapT<cluster> >,dim> > CubSet;
  typedef CubCellSetT<EuclBitSetT<BitSetT<BitmapT<cluster> >,dim> > CubCelSet;
  typedef CRef<CubSet> CubSetCR;
  typedef CRef<CubCelSet> CubCelSetCR;


  CubCelSetCR cubCelSetCR(new CubCelSet);
  CubSetCR cubSetCR(new CubSet);

  switch(fileType){
    case bin:{
      if(fullCubes){
        CubSet cubSet;
        cubSet.readBmp(inFileName);
        swap(cubSet,cubSetCR());
      }else{
        CubCelSet cubCelSet;
        cubCelSet.readBmp(inFileName);
        swap(cubCelSet,cubCelSetCR());
      }
    }
    break;
    case plain:
    case setOfFullCubes:
    case setOfCubes:{
      if(fullCubes){
        std::ifstream in;
        in.open(inFileName,ios::in);
        BmpCubSetBuilder<CubSet> csb(cubSetCR);
        readCubicalSet(in,csb);
      }else{
        std::ifstream in;
        in.open(inFileName,ios::in);
        BmpCubCelSetBuilder<CubCelSet> csb(cubCelSetCR);
        readCubicalSet(in,csb);
      }
    }
    break;
    default:
      throw "Unrecognized file type\n";
  }

  std::ofstream out;
  out.open(outFileName,ios::out);
  if(fullCubes){
    out << cubSetCR();
  }else{
    out << cubCelSetCR();
  }
}




void toCub(const char* inFileName,const char* outFileName){
  Stopwatch swRead;
  std::ifstream in;
  in.open(inFileName,ios::in);
  if(!in.good()){
    std::string s;
    s << "Unable to open file " << inFileName << " for reading\n";
    throw std::runtime_error(s.c_str());
  }

  CubSetBuilder csb;
  readCubicalSet(in,csb,true); //true means only get dim and type
  in.close();
  std::cout << "Reading completed in " << swRead  << std::endl;

  unsigned int embDim=csb.getDim();
  FileType fileType=csb.getFileType();
  bool fullCubes=csb.onlyFullCubes();
  #define CONVERT(d) case d:  convert<d>(inFileName,outFileName,fileType,fullCubes);break;

  switch(embDim){
    CONVERT(2)
    CONVERT(3)
    CONVERT(4)
    CONVERT(5)
    CONVERT(6)
    CONVERT(7)
    CONVERT(8)
    CONVERT(9)
    CONVERT(10)
    CONVERT(11)
    CONVERT(12)
    CONVERT(13)
    CONVERT(14)
    #undef CONVERT
    default:
      throw "toCub: unsupported dimension\n";
  }
}
/// @}

#endif //_TOCUB_HPP_
