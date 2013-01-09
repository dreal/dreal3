/****                              ****/
/**** (c) Marian Mrozek 2010       ****/

#include <iostream>

#include <cstdlib>
#include <iomanip>

//#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/homologicalAlgebra/readCubicalSet.hpp"
#include "capd/homologicalAlgebra/RepCubSetBuilder.hpp"
#include "capd/repSet/RepSet.h"
#include "capd/repSet/ElementaryCube.h"

//typedef unsigned long int cluster;
//typedef BitSetT<BitmapT<cluster> > BitSet;
//typedef EuclBitSetT<BitSet,embeddingDim> EuclBitSet;

int main(int argc,char* argv[]){
  using namespace std;
  typedef RepSet<ElementaryCube> RepSetType;

  try{
    CRef<RepSetType> repSetCR(new RepSetType());
    std::ifstream in;
    in.open(argv[1],ios::in);
    RepCubSetBuilder<RepSetType> csb(repSetCR);
    readCubicalSet(in,csb);
    std::cout << "\n------------\nGot " << csb.size() << " cubes\n------------\n";
    if(repSetCR().size()<300){
      std::cout << repSetCR() << std::endl;
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
