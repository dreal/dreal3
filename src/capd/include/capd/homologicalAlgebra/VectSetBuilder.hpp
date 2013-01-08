/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file VectSetBuilder.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#include <fstream>

#include "capd/auxil/CRef.h"
#include "capd/bitSet/EmbDimException.h"
#include "capd/auxil/stringOstream.h"
#include "capd/homologicalAlgebra/CubSetBuilder.h"

class VectSetBuilder : public CubSetBuilder{
  public:

    typedef std::vector<int> intVect;
    typedef std::vector<intVect> SetDataType;

    VectSetBuilder(){}

    VectSetBuilder(
      CRef<SetDataType> A_setDataCR
    ):
      fullCubes(true),
      setDataCR(A_setDataCR)
    {}

    bool isBoundingBoxNeeded(){
      return false;
    }

    void setFullCubes(bool b){
      fullCubes=b;
    }

    void setDim(int A_embDim){
      embDim=A_embDim;
    }

    void setBoundingBox(int A_cmin[],int A_cmax[]){
    }

    void addCell(int coords[]){
      intVect data(embDim);
      for(int i=0;i<embDim;++i){
        data[i]=coords[i]-cmin[i];
      }
      setDataCR().push_back(data);
    }

/*
    void finalize(){
    }
*/

    void show(){
      std::cout << "Set of coordinates:\n";
      std::cout << setDataCR();
    }
    int size(){
      return setDataCR().size();
    }


  protected:
//    bool fullCubes;
    CRef<SetDataType> setDataCR;
    int embDim;
};

/* ------------------------  ------------------------ */

struct VectMapBuilder : public VectSetBuilder{
    typedef std::vector<std::pair<bool,intVect> > MapDataType;
    typedef std::vector<int> intVect;
  public:

    VectMapBuilder(){}

    void setDomDim(int A_domEmbDim){
      domEmbDim=A_domEmbDim;
      locDomData.reserve(domEmbDim);
      cDomMin.reserve(domEmbDim);
      cDomMax.reserve(domEmbDim);
      for(int i=0;i<domEmbDim;++i){
        cDomMin.push_back(INT_MAX);
        cDomMax.push_back(INT_MIN);
      }
    }
    void setRngDim(int A_rngEmbDim){
      rngEmbDim=A_rngEmbDim;
      locRngData.reserve(rngEmbDim);
      cRngMin.reserve(domEmbDim);
      cRngMax.reserve(domEmbDim);
      for(int i=0;i<domEmbDim;++i){
        cRngMin.push_back(INT_MAX);
        cRngMax.push_back(INT_MIN);
      }
    }

    void addDomCell(int coords[]){
      for(int i=0;i<domEmbDim;++i){
        locDomData.push_back(coords[i]);
        if(coords[i] > cDomMax[i]) cDomMax[i]=coords[i];
        if(coords[i] < cDomMin[i]) cDomMin[i]=coords[i];
      }
      mapData.push_back(std::pair<bool,intVect>(false,locDomData));
    }

    void addRngCell(int coords[]){
      for(int i=0;i<rngEmbDim;++i){
        locRngData.push_back(coords[i]);
        if(coords[i] > cRngMax[i]) cRngMax[i]=coords[i];
        if(coords[i] < cRngMin[i]) cRngMin[i]=coords[i];
      }
      mapData.push_back(std::pair<bool,intVect>(true,locRngData));
    }

    void addCell(int coords[]){
    }

    void finalize(){
    }

   void show(){
      std::cout << "Set of map coordinates:\n";
      std::cout << this->setDataCR();
    }

  public:
    int domEmbDim,rngEmbDim;
    intVect locDomData;
    intVect locRngData;
    MapDataType mapData;
    intVect cDomMin,cDomMax,cRngMin,cRngMax;
};
