/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file MVCelMapCrHom.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2010 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_MVCELMAPCRHOM_H_)
#define _MVCELMAPCRHOM_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <exception>
#include <stdexcept>
#include <new>
using namespace std;

#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/auxil/ofstreamcout.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/memSize.h"
#include "capd/auxil/CRef.h"
#include "capd/auxil/stringOstream.h"


extern ofstreamcout fcout;

#include "capd/vectalg/MatrixSlice.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"


#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubCellSet.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
#include "capd/homologicalAlgebra/acyclicConfigs.hpp"
#include "capd/homologicalAlgebra/ProjChainMap.hpp"
#include "capd/homologicalAlgebra/ChainMapCrHom.hpp"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"

#include "capd/bitSet/ReductionPairT.h"
#include "capd/bitSet/CubFaceIndex.h"
#include "capd/bitSet/CubCellSetFiltrT.hpp"

#include "capd/homologicalAlgebra/FreeChainComplex.hpp"
#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.hpp" // temporarily here, should be compiled into the library
#include "capd/repSet/ECellMDCodeT.h"

using namespace capd;
using namespace matrixAlgorithms;


// Compute the matrices of homology maps using the bases and chain
// equivalences stored in the provided filtrations of cubcellsets.
// On output a CRef to a vector of matrices (one matrix per homology
// dimension) is provided.
template<typename P_Graph, typename P_Dom, typename P_Rng, typename P_Scalar>
class MVCelMapCrHom{
  public:
    typedef P_Scalar ScalarType;
    typedef capd::vectalg::Matrix<ScalarType,0,0> MatrixType;

    typedef P_Graph GraphSetType;
    typedef typename GraphSetType::ReductorType GraphReductorType;
    typedef typename GraphReductorType::CubeFaceIndexType GraphGenType;
    typedef FreeModule<GraphGenType,MatrixType> GraphFreeModuleType;
    typedef FreeChainComplex<GraphFreeModuleType> GraphFreeChainComplexType;
    typedef CubCellSetFiltrT<GraphSetType,GraphFreeChainComplexType> GraphFiltrType;
    typedef ChainT<std::map<GraphGenType,ScalarType> > GraphChainType;

    typedef P_Dom DomSetType;
    typedef typename DomSetType::ReductorType DomReductorType;
    typedef typename DomReductorType::CubeFaceIndexType DomGenType;
    typedef FreeModule<DomGenType,MatrixType> DomFreeModuleType;
    typedef FreeChainComplex<DomFreeModuleType> DomFreeChainComplexType;
    typedef CubCellSetFiltrT<DomSetType,DomFreeChainComplexType> DomFiltrType;
    typedef ChainT<std::map<DomGenType,ScalarType> > DomChainType;

    typedef P_Rng RngSetType;
    typedef typename RngSetType::ReductorType RngReductorType;
    typedef typename RngReductorType::CubeFaceIndexType RngGenType;
    typedef FreeModule<RngGenType,MatrixType> RngFreeModuleType;
    typedef FreeChainComplex<RngFreeModuleType> RngFreeChainComplexType;
    typedef CubCellSetFiltrT<RngSetType,RngFreeChainComplexType> RngFiltrType;
    typedef ChainT<std::map<RngGenType,ScalarType> > RngChainType;

    typedef ProjChainMap<GraphChainType,DomChainType> ProjXChainMapType;
    typedef ProjChainMap<GraphChainType,RngChainType> ProjYChainMapType;

    typedef typename MatrixType::ColumnVectorType ColumnVectorType;


    /* ------------------------  ------------------------ */
    MVCelMapCrHom(
      CRef<GraphSetType> A_graphSetTypeCR,
      CRef<DomSetType> A_domSetTypeCR,
      CRef<RngSetType> A_rngSetTypeCR,
      bool A_preShave=true
    ):
      graphCR(A_graphSetTypeCR),
      domCR(A_domSetTypeCR),
      rngCR(A_rngSetTypeCR),
      chnMapMatrixCR(new std::vector<MatrixType>())
    {

      if(A_preShave){
        Stopwatch prsSw;
        std::cout << "Starting pre-shaving with " << domCR().cardinality()
            << " in dom and " << graphCR().cardinality() << " in graph." << std::endl;
        DomSetType shaved(domCR());
        domCR().shave();
        shaved-=domCR();
        graphCR().clearFiber(shaved);
        std::cout << "Finishing pre-shaving with " << domCR().cardinality()
            << " cells in dom and " << graphCR().cardinality() << " in graph." << std::endl;
        std::cout << " *** Preshaving completed in " << prsSw  << "\n";
      }


      Stopwatch grSw;
      graphFiltrCR=CRef<GraphFiltrType>(new GraphFiltrType(graphCR));
      std::cout << " *** Graph filtr construction completed in " << grSw  << "\n";
      Stopwatch domSw;
      domFiltrCR=CRef<DomFiltrType>(new DomFiltrType(domCR));
      std::cout << " *** Dom filtr construction completed in " << domSw  << "\n";
      Stopwatch rngSw;
      rngFiltrCR=CRef<RngFiltrType>(new RngFiltrType(rngCR));
      std::cout << " *** Rng filtr construction completed in " << rngSw  << "\n";

      Stopwatch mtrxSw;
      ProjXChainMapType projXChainMap(projXMap);
      ChainMapCrHom<GraphSetType,DomSetType,ScalarType,ProjXChainMapType> cmXCrHom(projXChainMap);
      CRef<std::vector<MatrixType> > projXMatrixCR=cmXCrHom.getHomMatrix(graphFiltrCR(),domFiltrCR());
      std::cout << " *** Matrix X construction completed in " << mtrxSw  << "\n";

std::cout << " --- X Proj --- " << std::endl;  // -- MM
std::cout << projXMatrixCR()[1] << std::endl;  // -- MM

      Stopwatch mtrySw;
      ProjYChainMapType projYChainMap(projYMap);
      ChainMapCrHom<GraphSetType,RngSetType,ScalarType,ProjYChainMapType> cmYCrHom(projYChainMap);
      CRef<std::vector<MatrixType> > projYMatrixCR=cmYCrHom.getHomMatrix(graphFiltrCR(),rngFiltrCR());
      std::cout << " *** Matrix Y construction completed in " << mtrySw  << "\n";

std::cout << " --- Y Proj --- " << std::endl;   // -- MM
std::cout << projYMatrixCR()[1] << std::endl;       // -- MM

      Stopwatch mtrSw;
      for(unsigned int q=0;q<projXMatrixCR().size();++q){
        MatrixType& a=projXMatrixCR()[q];
        MatrixType& b=projYMatrixCR()[q];
        unsigned int m=a.numberOfRows();
        unsigned int n=a.numberOfColumns();
        if(m!=n){
/*
          std::cout << " --- Got wrong matrix in dim " << q << " ---\n";
          std::cout << graphFiltrCR() << std::endl;
          std::cout << domFiltrCR() << std::endl;
          std::cout << a << std::endl;
*/
          throw std::runtime_error("MVCelMapCrHom::getHomMatrix: mv map is not acyclic!!");
        }
        MatrixType aInv(n,n);
        if(!capd::matrixAlgorithms::invert(a,aInv)){
          throw std::runtime_error("MVCelMapCrHom::getHomMatrix: mv map is not acyclic!");
        }
        chnMapMatrixCR().push_back(MatrixType(n,n));
        chnMapMatrixCR()[q]=b*aInv;
      }
      std::cout << " *** Matrix of hom map construction completed in " << mtrSw  << "\n";
    }

    /* ------------------------  ------------------------ */
/*  // For XY order in graph - keep it just in case - needs changes in 2 other places
    static DomGenType projXMap(GraphGenType graphGen){
      return DomGenType(graphGen,false);// false for projection XxY -> X
    }
    static RngGenType projYMap(GraphGenType graphGen){
      return RngGenType(graphGen,true); // true for projection XxY -> Y
    }
*/
    // For YX order in graph - more efficient
    static DomGenType projXMap(GraphGenType graphGen){
      return DomGenType(graphGen,true); // true for projection YxX -> X
    }
    static RngGenType projYMap(GraphGenType graphGen){
      return RngGenType(graphGen,false);// false for projection YxX -> Y
    }

    /* ------------------------  ------------------------ */
    CRef<std::vector<MatrixType> > getHomMatrix(
    ){
      return chnMapMatrixCR;
    }


    /* ------------------------  ------------------------ */
    std::string getHomMatrixSignature(
    ){
      std::string result;

/*
      result << "Homology of graph is: \n\n" << graphFiltrCR()  << "\n";
      result << "Homology of domain is: \n\n" << domFiltrCR()  << "\n";
      result << "Homology of range is: \n\n" << rngFiltrCR()  << "\n";
*/

      result << "The matrix of the chain map is: \n\n" << "\n";
      for(int q=0;q<=rngFiltrCR().TopDim();++q){
        result << "  -- Dimension " << q << " -- " << "\n";
        result << chnMapMatrixCR()[q] << "\n";
      }
      return result;
    }
  private:
    CRef<GraphSetType> graphCR;
    CRef<DomSetType> domCR;
    CRef<RngSetType> rngCR;
    CRef<GraphFiltrType> graphFiltrCR;
    CRef<DomFiltrType> domFiltrCR;
    CRef<RngFiltrType> rngFiltrCR;
    CRef<std::vector<MatrixType> > chnMapMatrixCR;
};// MVCelMapCrHom

#endif //_MVCELMAPCRHOM_H_
/// @}

