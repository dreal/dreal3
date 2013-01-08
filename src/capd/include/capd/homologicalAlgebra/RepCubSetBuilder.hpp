#if !defined(_REPCUBSETBUILDER_H_)
#define _REPCUBSETBUILDER_H_

#include <fstream>

#include "capd/auxil/CRef.h"
#include "capd/repSet/RepSet.h"
#include "capd/homologicalAlgebra/CubSetBuilder.h"

template<typename P_RepSet>
class RepCubSetBuilder : public CubSetBuilder{
    typedef P_RepSet RepSetType;
    typedef typename RepSetType::ElementarySetType ElementarySetType;
  public:
    RepCubSetBuilder(CRef<RepSetType> A_repSetCR):repSetCR(A_repSetCR){}

    void setBoundingBox(int A_cmin[],int A_cmax[]){
      // Dostarcza boundingBox
        for(int i=0;i<embDim;++i){
          cmin.push_back(A_cmin[i]);
          cmax.push_back(A_cmax[i]);
        }
    }
    void addCell(int coords[]){
      // Dostarcza n wspolrzednych kostki, gdzie n to wymiar wlozenia
      // W przypadku gdy setFullCubes dostarczylo false wspolrzedne sa parzyste
      // dla przedzialow zdegenerowanych, a w przeciwnym razie sa nieparzyste
      // W przypadku gdy setFullCubes dostarczylo true dostarczane sa wspolrzedne
      // lewego dolnego rogu pelnej kostki
      if(fullCubes){
        std::vector<int> data;
        data.reserve(embDim);
        for(int i=0;i<embDim;++i){
          data.push_back(coords[i]);
        }
        repSetCR().insert(ElementarySetType(data));
      }else{
        std::vector<int> data;
        bool* parity=new bool[embDim];
        data.reserve(embDim);
        for(int i=0;i<embDim;++i){
          data.push_back(coords[i]/2);
          parity[i]=(coords[i] % 2);
        }
        repSetCR().insert(ElementarySetType(&data[0],parity,embDim));
      }
    }

    void show(){
      std::cout << "Cubical set with bounding box:\n";
      for(int i=0;i<embDim;++i){
        if(i) std::cout << "x";
        std::cout << "[" << cmin[i] << "," << cmax[i] << "]";
      }
      std::cout << "\n";
      std::cout << repSetCR();
    }
    int size(){
      return repSetCR().size();
    }


  private:
    CRef<RepSetType> repSetCR;
    std::vector<int> cmin,cmax;
};

#endif //_REPCUBSETBUILDER_H_

