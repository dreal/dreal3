/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrbMapHom.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*
     This program computes the matrix of the homlogy map of
     a projection from the domain to the range space provided on input
*/


#include <iostream>

#include <cstdlib>
#include <iomanip>

#include "capd/auxil/AdvStopwatch.h"
#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/homologicalAlgebra/readCubicalSet.hpp"
#include "capd/homologicalAlgebra/BmpCubCelSetBuilder.hpp"
#include "capd/homologicalAlgebra/MVCelMapCrHom.hpp"
#include "capd/repSet/ECellMDCodeT.h"


const int domEmbDim=3;
const int rngEmbDim=3;
/*
const int domEmbDim=2;
const int rngEmbDim=2;
*/
/*
const int domEmbDim=4;
const int rngEmbDim=4;
*/
const int graphEmbDim=domEmbDim+rngEmbDim;

typedef int ScalarType;
//typedef unsigned long int cluster;
typedef unsigned long long longcluster;
typedef ECellMDCodeT<longcluster,graphEmbDim> GraphGenType;
//typedef ECellMDCodeT<cluster,graphEmbDim> GraphGenType;
typedef ECellMDCodeT<cluster,domEmbDim> DomGenType;
typedef ECellMDCodeT<cluster,rngEmbDim> RngGenType;

typedef BitSetT<BitmapT<cluster> > BitSet;
typedef EuclBitSetT<BitSet,domEmbDim> DomEuclBitSet;
typedef EuclBitSetT<BitSet,rngEmbDim> RngEuclBitSet;
typedef EuclBitSetT<BitSet,graphEmbDim> GraphEuclBitSet;
typedef CubCellSetT<DomEuclBitSet,ReductionPairT<DomGenType> > DomCubCelSet;
typedef CubCellSetT<RngEuclBitSet,ReductionPairT<RngGenType> > RngCubCelSet;
typedef CubCellSetT<GraphEuclBitSet,ReductionPairT<GraphGenType> > GraphCubCelSet;

typedef BmpCubCelMVMapBuilder<GraphCubCelSet,DomCubCelSet,RngCubCelSet> BmpCubCelMVMapBuilderType;
typedef MVCelMapCrHom<GraphCubCelSet,DomCubCelSet,RngCubCelSet,ScalarType> MVMapCrHomType;

ofstreamcout fcout;

int main(int argc,char* argv[]){
  using namespace std;

  try{
    fcout.open("out.txt");
    fcout.turnOn();

    Stopwatch swTot,swRead;
    AdvStopwatch swTot2;
    std::fstream in;
    in.open(argv[1],ios::in);

    CRef<GraphCubCelSet> graphCR=CRef<GraphCubCelSet>(new GraphCubCelSet());
    CRef<DomCubCelSet> domCR=CRef<DomCubCelSet>(new DomCubCelSet());
    CRef<RngCubCelSet> rngCR=CRef<RngCubCelSet>(new RngCubCelSet());

    BmpCubCelMVMapBuilderType csb(graphCR,domCR,rngCR);
    readCubicalMap(in,csb);
    std::cout << "Reading completed in " << swRead  << "\n";

std::cout << "  === Graph covering is " << (graphCR().cardinality()*100.0)/(8.*graphCR().Length()) << "%\n";
    Stopwatch swComp;
    AdvStopwatch swComp2;

    bool preShave=(argc>2 ? true : false);

    MVMapCrHomType mapCrHom(graphCR,domCR,rngCR,preShave);
    swComp2.stop();

    std::string s=mapCrHom.getHomMatrixSignature();
    std::cout << s << std::endl;
    std::cout << "Computation completed in " << swComp2  << "\n";
    std::cout << "Total time (including input/output time) " << swTot  << "\n";

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




/// @}

