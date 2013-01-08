/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BmpCubCelSetBuilder.hpp
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
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"
#include "capd/bitSet/CubSetT.h"
#include "capd/bitSet/CubCellSetT.hpp"
#include "capd/repSet/RepSet.h"
#include "capd/repSet/ElementaryCube.h"
#include "capd/bitSet/EmbDimException.h"
#include "capd/auxil/stringOstream.h"
#include "capd/homologicalAlgebra/CubSetBuilder.h"

template<typename P_Set>
class BmpCubCelSetBuilder : public CubSetBuilder{
  public:
    typedef P_Set SetType;
    static const int embDim=SetType::theDim;


    BmpCubCelSetBuilder(
      CRef<SetType> A_setCR
    ):
//      fullCubes(true),
      setCR(A_setCR),
      cmin(embDim),
      cmax(embDim),
      boundingBox(embDim)
    {}

    bool isBoundingBoxNeeded(){
      return true;
    }

    void setFullCubes(bool b){
      fullCubes=b;
    }
    void setDim(int A_embDim){
      if(A_embDim!=embDim){
        string s;
//        s << "BmpCubCelSetBuilder: incorrect embDim, expected " << embDim << " got " << A_embDim << "\n";
        throw EmbDimException("BmpCubCelSetBuilder: incorrect embDim");
      }
    }
    void setBoundingBox(int A_cmin[],int A_cmax[]){
      for(int i=0;i<embDim;++i){
        if(fullCubes){
          cmin[i]=2*A_cmin[i];
          cmax[i]=2*A_cmax[i]+2;
        }else{
          cmin[i]=A_cmin[i];
          cmax[i]=A_cmax[i];
        }
        boundingBox[i]=cmax[i]-cmin[i]+1;
      }

      SetType internalSet(&boundingBox[0],true); // true means clear
      swap(internalSet,setCR());
    }
    void addCell(int coords[]){
      std::vector<int> data(embDim);
      for(int i=0;i<embDim;++i){
        if(fullCubes){
          data[i]=2*coords[i]+1-cmin[i];
        }else{
          data[i]=coords[i]-cmin[i];
        }
      }
      setCR().insert(&data[0]);
    }

    void finalize(){
      if(fullCubes){
        setCR().fillWithSubEmbDimCells();
      }else if(!openCells){
std::cout << "Filling" << std::endl;
        setCR().fillWithBoundaries();
      }
    }

    void show(){
      std::cout << "Cubical set with bounding box:\n";
      for(int i=0;i<embDim;++i){
        if(i) cout << "x";
        cout << "[" << cmin[i] << "," << cmax[i] << "]";
      }
      cout << "\n";
      std::cout << setCR();
    }
    int size(){
      return setCR().cardinality();
    }


  protected:
//    bool fullCubes;
    CRef<SetType> setCR;
    std::vector<int> cmin,cmax,boundingBox;
};

/* ------------------------  ------------------------ */

template<typename P_Set,typename P_DomSet,typename P_RngSet>
class BmpCubCelMVMapBuilder : public BmpCubCelSetBuilder<P_Set>{
    typedef typename BmpCubCelSetBuilder<P_Set>::SetType SetType;
    typedef P_DomSet DomSetType;
    typedef P_RngSet RngSetType;
  public:
    static const int embDim=SetType::theDim;
    static const int domEmbDim=DomSetType::theDim;
    static const int rngEmbDim=RngSetType::theDim;


    BmpCubCelMVMapBuilder(
      CRef<SetType> A_setCR,
      CRef<DomSetType> A_domSetCR,
      CRef<RngSetType> A_rngSetCR
    ):
      BmpCubCelSetBuilder<P_Set>(A_setCR),
      domSetCR(A_domSetCR),
      rngSetCR(A_rngSetCR)
    {}


    void setDomDim(int A_domEmbDim){
      if(A_domEmbDim!=domEmbDim) throw EmbDimException("BmpCubCelSetBuilder: incorrect domEmbDim\n");
    }
    void setRngDim(int A_rngEmbDim){
      if(A_rngEmbDim!=rngEmbDim) throw EmbDimException("BmpCubCelSetBuilder: incorrect rngEmbDim\n");
    }
    void setBoundingBox(int A_cmin[],int A_cmax[]){
      BmpCubCelSetBuilder<P_Set>::setBoundingBox(A_cmin,A_cmax);

      DomSetType internalDomSet(&this->boundingBox[0],true); // true means clear
      swap(internalDomSet,domSetCR());

      RngSetType internalRngSet(&this->boundingBox[domEmbDim],true); // true means clear
      swap(internalRngSet,rngSetCR());
    }

    void addDomCell(int coords[]){
      std::vector<int> data(domEmbDim);
      for(int i=0;i<domEmbDim;++i){
        if(this->fullCubes){
          data[i]=2*coords[i]+1-this->cmin[i];
        }else{
          data[i]=coords[i]-this->cmin[i];
        }
      }
      domSetCR().insert(&data[0]);
    }

    void addRngCell(int coords[]){
      std::vector<int> data(rngEmbDim);
      for(int i=0;i<rngEmbDim;++i){
        if(this->fullCubes){
          data[i]=2*coords[i]+1-this->cmin[i+domEmbDim];
        }else{
          data[i]=coords[i]-this->cmin[i+domEmbDim];
        }
      }
      rngSetCR().insert(&data[0]);
    }

    void finalize(){
      if(this->fullCubes){
        BmpCubCelSetBuilder<P_Set>::finalize();
        domSetCR().fillWithSubEmbDimCells();
        rngSetCR().fillWithSubEmbDimCells();
      }
    }

   void show(){
      std::cout << "MV cubical map with bounding box of graph:\n";
      for(int i=0;i<embDim;++i){
        if(i) cout << "x";
        cout << "[" << this->cmin[i] << "," << this->cmax[i] << "]";
      }
      cout << "\n";
      std::cout << this->setCR();
    }



  private:
    CRef<DomSetType> domSetCR;
    CRef<RngSetType> rngSetCR;
};
