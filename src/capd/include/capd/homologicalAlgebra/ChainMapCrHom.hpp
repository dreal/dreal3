/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ChainMapCrHom.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2010 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*
This file is under construction
This file is an adaptation of ChainMapCrHom.cpp to arbitrary chain maps
*/
#if !defined(_CHAINMAPCRHOM_H_)
#define _CHAINMAPCRHOM_H_

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

using namespace capd;
using namespace matrixAlgorithms;

#include "capd/homologicalAlgebra/homologicalAlgebra.hpp"
#include "capd/homologicalAlgebra/readCubCellSet.hpp"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"
#include "capd/homologicalAlgebra/acyclicConfigs.hpp"
//#include "capd/homologicalAlgebra/FreeModule.h"

#include "capd/bitSet/ReductionPairT.h"
#include "capd/bitSet/CubFaceIndex.h"
#include "capd/bitSet/CubCellSetFiltrT.hpp"

#include "capd/homologicalAlgebra/FreeChainComplex.hpp"
#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.hpp" // temporarily here, should be compiled into the library
#include "capd/repSet/ECellMDCodeT.h"

// Compute the matrices of homology maps using the bases and chain
// equivalences stored in the provided filtrations of cubcellsets.
// On output a cref to a vector of matrices (one matrix per homology
// dimension) is provided.
template<typename P_DomSet, typename P_RngSet, typename P_Scalar, typename P_ChainMap>
class ChainMapCrHom{
  public:
    typedef P_Scalar ScalarType;
    typedef P_ChainMap ChainMapType;
    typedef capd::vectalg::Matrix<ScalarType,0,0> MatrixType;

    typedef P_DomSet DomSetType;
    typedef typename DomSetType::ReductorType DomReductorType;
    typedef typename DomReductorType::CubeFaceIndexType DomGenType;
    typedef FreeModule<DomGenType,MatrixType> DomFreeModuleType;
    typedef FreeChainComplex<DomFreeModuleType> DomFreeChainComplexType;
    typedef CubCellSetFiltrT<DomSetType,DomFreeChainComplexType> DomFiltrType;
    typedef ChainT<std::map<DomGenType,ScalarType> > DomChainType;

    typedef P_RngSet RngSetType;
    typedef typename RngSetType::ReductorType RngReductorType;
    typedef typename RngReductorType::CubeFaceIndexType RngGenType;
    typedef FreeModule<RngGenType,MatrixType> RngFreeModuleType;
    typedef FreeChainComplex<RngFreeModuleType> RngFreeChainComplexType;
    typedef CubCellSetFiltrT<RngSetType,RngFreeChainComplexType> RngFiltrType;
    typedef ChainT<std::map<RngGenType,ScalarType> > RngChainType;

//    typedef CRef<RngChainType> (*ChainMapType)(const DomChainType&);

    typedef typename MatrixType::ColumnVectorType ColumnVectorType;

    /* ------------------------  ------------------------ */
    ChainMapCrHom(ChainMapType& A_chainMap):chainMap(A_chainMap){
    }

    /* ------------------------  ------------------------ */
    CRef<std::vector<MatrixType> > getHomMatrix(
      const DomFiltrType& A_DomHFiltr,
      const RngFiltrType& A_RngHFiltr
    ){
      // A shorthand for the vector (indexed by homology dimension) of vectors
      // (indexed by consecutive numbers) of chains forming the basis of homology of the domain
      const std::vector<std::vector<DomChainType> >& domBaseHomChain=A_DomHFiltr.BaseHomologyChain();
      // A shorthand for the vector (indexed by homology dimension) of vectors
      // (indexed by consecutive numbers) of simplified (reduced) chains forming the basis
      // of homology of the superspace after all reductions (but not those for which Smith was needed, see below)
      const std::vector<std::vector<RngChainType> >& rngSimplifiedBaseHomChain=A_RngHFiltr.SimplifiedBaseHomologyChain();
      // A shorthand to the quotient graded module of the part of homology of the reduced range
      // which had to be treated by Smith algorithm (not reduced by coreduction algorithm or algebraic reductions algorithm)
      const QuotientGradedModule<RngFreeModuleType>& rngFHM=A_RngHFiltr.filteredHomModule();

      int topDimFromSmith=rngFHM.TopDim();
      int topDimSimple=rngSimplifiedBaseHomChain.size()-1;
      int topDim=std::max(topDimSimple,topDimFromSmith);

      // prepare the vector container for the matrices to be computed
      CRef<std::vector<MatrixType> > chnMapMatrixCR(new std::vector<MatrixType>()) ;
      // for every grade dimension
      for(int q=0;q<=topDim;++q){
// -- MM  std::cout << " *** Computing chain map on grade " << q << std::endl;
        // this will be the number of columns in the matrix
        unsigned int n=domBaseHomChain[q].size();
        // this will be the number of rows in the matrix
        unsigned int m=rngSimplifiedBaseHomChain[q].size();
        // prepare an uninitialized matrix
        chnMapMatrixCR().push_back(MatrixType(m,n));
        // for every basis vector in the homology of the domain
        for(unsigned int j=0;j<n;++j){
          // cImg contains a working copy of the homology generator
// -- MM  std::cout << "  Arg is " << domBaseHomChain[q][j] << std::endl;
          CRef<RngChainType> cImgCR=chainMap(domBaseHomChain[q][j]);       // the image of the j-th base cycle in dim q of the domain
          RngChainType& cImg=cImgCR();                                 // reference to the image of the j-th base cycle in dim q of the domain
// -- MM  std::cout << "  Val is " << cImg << std::endl;

                                                                      // in the chain map
          A_RngHFiltr.reduce(cImg);                                   // its reduction via the filter of the range
          ColumnVectorType cVect;                                     // this will contain the vector of coefficients of the reduced cImg
                                                                      // in the basis of the chain group of the reduced range
          ColumnVectorType cHomCoefVect;                              // this will contain the vector of coefficients of the
                                                                      // homolopgy class of the reduced cImg
                                                                      // in the basis of the homology of the reduced range
          // i0 is the number of entries coming from Smith generators
          unsigned int i0=0;
          // first we insert entries from Smith generators
          if(q<=topDimFromSmith){
            i0=rngFHM.component(q).numberOfGenerators();
            rngFHM.component(q).BaseModulePtr()->coefVector(cImg,cVect);   // cVect stores the vector of coefficients
                                                                        // of the reduced chain cImg in the base of the chain group
            rngFHM.component(q).coefVectorForCycle(cVect,cHomCoefVect); // the vector of coefficients of the homology of cImg
                                                                        // in the homology base of the reduced range
            for(unsigned int i=0;i<i0;++i){
              chnMapMatrixCR()[q][i][j]=cHomCoefVect[i];                  // insert the respective coefficient
            }
          }
          // and here we insert entries from simple (non-Smith, obtained directly from reduction) generators
          if(q<=topDimSimple){
            for(unsigned int i=i0;i<m;++i){
              // The simple homology generators as chains have always exactly one non-trivial element
              // of the form (g,1), where g is the respective chain group generator
              // We insert cImg.at(g), where g==rngSimplifiedBaseHomChain[q][i].begin()->first (the second element is one)
              chnMapMatrixCR()[q][i][j]=cImg.at(rngSimplifiedBaseHomChain[q][i].begin()->first);
            }
          }
        }
      }
      return chnMapMatrixCR;
    }


    /* ------------------------  ------------------------ */
    std::string getHomMatrix(CRef<DomSetType> A_domSetCR,CRef<RngSetType> A_rngSetCR){
      std::string result;
      Stopwatch swTot;
      DomFiltrType domHomFiltr(A_domSetCR);
      RngFiltrType rngHomFiltr(A_rngSetCR);

      CRef<std::vector<MatrixType> > chnMapMatrixCR=getHomMatrix(domHomFiltr,rngHomFiltr);


      result << "Homology of domain is: \n\n" << domHomFiltr  << "\n";
      result << "Homology of range is: \n\n" << rngHomFiltr  << "\n";
      result << "The matrix of the chain map is: \n\n" << "\n";
      for(int q=0;q<=rngHomFiltr.TopDim();++q){
        result << "  -- Dimension " << q << " -- " << "\n";
        result << chnMapMatrixCR()[q] << "\n";
      }
      result << "Computation completed in " << swTot  << "\n";
      return result;
    }

  private:
    const ChainMapType& chainMap;

};// ChainMapCrHom

#endif //_CHAINMAPCRHOM_H_
/// @}

