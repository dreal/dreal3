/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file MVFullMapPreprocess.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2010 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*
   Projekt ma na celu przyspieszenie liczenia homologii odwzorowañ
   poprzez uwzglêdnienie shave poprzez LT na poziomie pelnych kostek
   w dziedzinie.
   Rozpoczete, ale przerwane. MM 2010-06-01
*/

#if !defined(_MVFULLMAPPREPROCESS_H_)
#define _MVFULLMAPPREPROCESS_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <stdexcept>
#include <new>
using namespace std;

//#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"
#include "capd/auxil/stringOstream.h"


extern ofstreamcout fcout;



#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
#include "capd/homologicalAlgebra/acyclicConfigs.hpp"
#include "capd/homologicalAlgebra/VectSetBuilder.hpp"


using namespace capd;
using namespace matrixAlgorithms;


template<typename P_Graph, typename P_Dom, typename P_Rng, domEmbDim, int rngEmbDim>
class MVFullMapPreprocess{
  public:

    const int graphEmbDim=domEmbDim+rngEmbDim;

    typedef P_Graph GraphCelSetType;
    typedef P_Dom DomCelSetType;
    typedef P_Rng RngCelSetType;

    typedef int ScalarType;
    typedef unsigned long int cluster;

    typedef BitSetT<BitmapT<cluster> > BitSet;
    typedef EuclBitSetT<BitSet,domEmbDim> DomEuclBitSet;
    typedef EuclBitSetT<BitSet,rngEmbDim> RngEuclBitSet;

    typedef CubSetT<DomEuclBitSet,ReductionPairT<DomGenType> > DomCubSet;
    typedef CubSetT<RngEuclBitSet,ReductionPairT<RngGenType> > RngCubSet;


    typedef BmpCubCelMVMapBuilder<GraphCubCelSet,DomCubCelSet,RngCubCelSet> BmpCubCelMVMapBuilderType;
    typedef MVCelMapCrHom<GraphCubCelSet,DomCubCelSet,RngCubCelSet,ScalarType> MVMapCrHomType;

    typedef std::vector<int> intVect;
    typedef std::vector<intVect> SetDataType;

    /* ------------------------  ------------------------ */
    MVFullMapPreprocess(
      CRef<GraphCelSetType> A_graphCelSetTypeCR,
      CRef<DomCelSetType> A_domCelSetTypeCR,
      CRef<RngCelSetType> A_rngCelSetTypeCR,
      CRef<VectSetBuilder> A_vsbCR;
    ):
      graphCelSetCR(A_graphCelSetTypeCR),
      domCelSetCR(A_domCelSetTypeCR),
      rngCelSetCR(A_rngCelSetTypeCR),
      vsbCR(A_vsbCR)
    {

      {  // local to save memory

        int domSize[domEmbDim];
        for(int i=0;i<domEmbDim;++i){
          domSize[i]=vsbCR().cDomMax[i]-vsbCR().cDomMin[i]+3; // +2 added for collar
        }
        DomCubSet domCubSet(domSize,true); // true for clear

        int rngSize[rngEmbDim];
        for(int i=0;i<rngEmbDim;++i){
          rngSize[i]= 2*(vsbCR().cDomMax[i]-vsbCR().cDomMin[i])+3; // +2 to adjust the change form ful to cel setting
        }
        RngCelSetType rngCelSet(rngSize,true); // true for clear

        SetDataType& vsbMapData=vsbCR().mapData;
        typename SetDataType::const_iterator const_iterator;
        SetDataType& vsbMapData=vsbCR().mapData;
        for(const_iterator it=vsbMapData.begin();it!=vsbMapData.end();++it){
          if(!it->first){
            for(int i=0;i<domEmbDim;++i){
              locDomData[i]=it->second[i]-vsbCR().cDomMin[i]+1;
            }
            domCubSet.insert(locDomData);
          }else{
            for(int i=0;i<rngEmbDim;++i){
              locDomData[i]=2*(it->second[i]-vsbCR().cDomMin[i])+1;
            }
            rngCelSet.insert(locDomData);
          }
        }

        domCubSet.shave();
        DomCubSet diff(domCubSet);
        diff-=domCubSet;
      }

    }

  private:
    CRef<GraphCelSetType> graphCelSetCR;
    CRef<DomCelSetType> domCelSetCR;
    CRef<RngCelSetType> rngCelSetCR;
    CRef<VectSetBuilder> vsbCR;
    intVect locDomData;
    intVect locRngData;
};// MVFullMapPreprocess

#endif //_MVFULLMAPPREPROCESS_H_
/// @}

