/****                              ****/
/**** (c) Marian Mrozek 2010       ****/
/****                              ****/

#include <iostream>

#include <cstdlib>
#include <iomanip>

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/homologicalAlgebra/readCubicalSet.hpp"
#include "capd/homologicalAlgebra/BmpCubCelSetBuilder.hpp"
#include "capd/repSet/ECellMDCodeT.h"


const int domEmbDim=2;
const int rngEmbDim=2;
const int graphEmbDim=domEmbDim+rngEmbDim;

typedef int ScalarType;
typedef unsigned long int cluster;
typedef ECellMDCodeT<cluster,domEmbDim> DomGenType;
typedef ECellMDCodeT<cluster,rngEmbDim> RngGenType;
typedef ECellMDCodeT<cluster,graphEmbDim> GraphGenType;

typedef BitSetT<BitmapT<cluster> > BitSet;
typedef EuclBitSetT<BitSet,domEmbDim> DomEuclBitSet;
typedef EuclBitSetT<BitSet,rngEmbDim> RngEuclBitSet;
typedef EuclBitSetT<BitSet,graphEmbDim> GraphEuclBitSet;
typedef CubCellSetT<DomEuclBitSet,ReductionPairT<DomGenType> > DomCubCelSet;
typedef CubCellSetT<RngEuclBitSet,ReductionPairT<RngGenType> > RngCubCelSet;
typedef CubCellSetT<GraphEuclBitSet,ReductionPairT<GraphGenType> > GraphCubCelSet;

typedef BmpCubCelMVMapBuilder<GraphCubCelSet,DomCubCelSet,RngCubCelSet> BmpCubCelMVMapBuilderType;

int main(int argc,char* argv[]){
  using namespace std;

  try{
    std::fstream in;
    in.open(argv[1],ios::in);

    CRef<GraphCubCelSet> graphCR=CRef<GraphCubCelSet>(new GraphCubCelSet());
    CRef<DomCubCelSet> domCR=CRef<DomCubCelSet>(new DomCubCelSet());
    CRef<RngCubCelSet> rngCR=CRef<RngCubCelSet>(new RngCubCelSet());

    BmpCubCelMVMapBuilderType csb(graphCR,domCR,rngCR);
    readCubicalMap(in,csb);

    std::cout << "\n------------\nGot " << csb.size() << " cubes\n------------\n";
    if(csb.size()<300){
      csb.show();
    }

  }catch(std::exception& e){
    std::cout << "Caught exception: " << e.what() << endl;
  }catch(std::string& s){
    std::cout << "Caught exception: " << s.c_str() << endl;
  }catch(const char* c){
    std::cout << "Caught exception: " << c << endl;
  }catch(...){
    std::cout << "Caught an unknown exception: " << endl;
  }
}
