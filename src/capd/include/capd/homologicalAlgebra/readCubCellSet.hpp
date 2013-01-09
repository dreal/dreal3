/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file readCubCellSet.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_READCUBCELLSET_H_)
#define _READCUBCELLSET_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <new>
using namespace std;

#include "capd/auxil/ofstreamcout.h"
extern ofstreamcout fcout;
#include "capd/bitSet/EuclBitSet.hpp"
#include "capd/bitSet/CubCellSetT.hpp"
#include "capd/bitSet/EmbDimException.h"

template <typename P_CubSet,typename P_CubCellSet>
CRef<P_CubCellSet> readCubCellSet(const char* fileName){
  std::fstream in;

  CRef<P_CubCellSet> cubCellSetCR(new P_CubCellSet());
//  CRef<P_CubCellSet> cubCellSetCR(new P_CubCellSet(2));

  bool binaryFile=false,representableSet=false;

  in.open(fileName,ios::in);
  if(!in.good()){
    // std::ostringstream s;
    fcout << "Unable to open file " << fileName << " for reading " << std::endl;
    exit(1);
    // throw std::runtime_error(s.str());
  }

  char c=in.get();
  if(c=='B') binaryFile=true;
  c=in.get();
  if(c=='R') representableSet=true;
  in.close();

  if(binaryFile){
    // fcout << "Reading binary file\n";
    if(representableSet){ // code for representable binary sets, needed for displaying representable sets
      P_CubCellSet cubCellSet;
      cubCellSet.readBmp(fileName);
      swap(cubCellSet,cubCellSetCR());
    }else{ // standard full cubical set
      // fcout << "Reading full cubset file\n";
      P_CubSet cubSet;
      cubSet.readBmp(fileName);
      P_CubCellSet cubCellSet(cubSet);
      swap(cubCellSet,cubCellSetCR());
    }
  }else{
    Stopwatch t;
    //  fcout << "Reading text file\n";
    in.open(fileName,ios::in);
    std::ios::pos_type startOfIn=in.tellg();
    enum SetType{unknown,fullCubical,cubical,representable} setType=unknown;
    try{
      P_CubSet cubSet;
      in >> cubSet;
      P_CubCellSet cubCellSet(cubSet);
      swap(cubCellSet,cubCellSetCR());
      setType=fullCubical;
    }catch(std::ios_base::failure){ // This was probably a representable set
      setType=representable;
    }catch(DimException){ // This was not a full cubical set, so we try to read an ordinary cubical set
      setType=cubical;
    }
    if(setType!=fullCubical){
      if(setType==cubical){
        const int dim=P_CubCellSet::BaseClass::theDim;
        in.clear();
        in.seekg(startOfIn);
        RepSet<ElementaryCube> eCubeRepSet;
        in >> eCubeRepSet;
        if(dim!=eCubeRepSet.embeddingDimension()) throw EmbDimException("operator>>(istream&,EuclBitSetT<P_BitSet,dim>::importRepSetOfElementaryCube): incorrect embedding dimension");
        typedef typename P_CubCellSet::BaseClass::BaseClass P_BitSet;
/*
  EuclBitSetT<P_BitSet,dim> cubSet(eCubeRepSet);
  P_CubCellSet cubCellSet(cubSet);
  swap(cubCellSet,cubCellSetCR());
*/
        CubCellSetT<EuclBitSetT<P_BitSet,dim> > cubCellSet(eCubeRepSet);
        swap(cubCellSet,cubCellSetCR());
      }
      if(setType==representable){
        const int dim=P_CubCellSet::BaseClass::theDim;
        in.clear();
        in.seekg(startOfIn);
        RepSet<ElementaryCell> eCubeRepSet;
        in >> eCubeRepSet;
        if(dim!=eCubeRepSet.embeddingDimension()) throw EmbDimException("operator>>(istream&,EuclBitSetT<P_BitSet,dim>::importRepSetOfElementaryCube): incorrect embedding dimension");
        typedef typename P_CubCellSet::BaseClass::BaseClass P_BitSet;
        CubCellSetT<EuclBitSetT<P_BitSet,dim> > cubCellSet(eCubeRepSet);
        swap(cubCellSet,cubCellSetCR());
      }
    }
    in.close();
    fcout << "Reading completed in " << t << std::endl;
  }
  int sizeCnt=cubCellSetCR().cardinality();
  if(sizeCnt==0){
    throw std::runtime_error("An empty set found on input ");
  }
  fcout << "Found " << sizeCnt << " cells with enclosing box: (";
  long double prod=1;
  int dim=cubCellSetCR().embDim();
//  for(int i=0;i<embeddingDim;++i){
  for(int i=0;i<dim;++i){
    int factor=cubCellSetCR().getUnpaddedWidth(i);
    prod*=factor;
    fcout << factor << " ";
  }
  int cf= int((double(sizeCnt)/prod)*100.0);
  fcout << ")\nCovering is: " << cf << "%\n";
  return cubCellSetCR;
}

#endif //_READCUBCELLSET_H_


/// @}

