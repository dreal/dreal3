/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file InclusionHomology.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_INCLUSIONHOMOLOGY_H_)
#define _INCLUSIONHOMOLOGY_H_

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

#include "capd/bitSet/ReductionPairT.h"
#include "capd/bitSet/CubFaceIndex.h"
#include "capd/bitSet/CubCellSetFiltrT.hpp"

#include "capd/homologicalAlgebra/FreeChainComplex.hpp"
#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.hpp" // temporarily here, should be compiled into the library
#include "capd/repSet/ECellMDCodeT.h"

// Compute the matrices of homology maps using the bases and chain
// equivalences stored in the provided filtrations of cubcellsets.
// On output a cref to a vector of matrices (one matrix per homology
// dimension is provided.
template<typename SCubCelSet, typename FreeChainComplexType>
struct InclusionHomology{
    typedef typename FreeChainComplexType::FreeModuleType FreeModuleType;
    typedef typename FreeModuleType::GeneratorType ElementaryCellType;
    typedef typename FreeModuleType::ScalarType ScalarType;
    typedef typename FreeModuleType::MatrixType MatrixType;
    typedef typename MatrixType::ColumnVectorType ColumnVectorType;
    typedef typename SCubCelSet::ReductorType ReductorType;
    typedef typename ReductorType::CubeFaceIndexType CubeFaceIndexType;
/*
    typedef ChainT<std::map<ElementaryCellType,int> > ChainType;
    typedef ChainT<std::map<int,int> > SparseIntVector;
*/
    typedef ChainT<std::map<ElementaryCellType,ScalarType> > ChainType;
    typedef ChainT<std::map<int,ScalarType> > SparseIntVector;
    typedef std::vector<SparseIntVector> SparseIntMatrix;
    typedef std::vector<CRef<SparseIntMatrix> >  GradedCRefSparseIntMatrix;

  /* ------------------------  ------------------------ */
  static CRef<std::vector<MatrixType> > CrbIncHom(
    const CubCellSetFiltrT<SCubCelSet,FreeChainComplexType>& A_subHFiltr,
    const CubCellSetFiltrT<SCubCelSet,FreeChainComplexType>& A_supHFiltr
  ){
/*  Changed to save memory, original set no longer stored in the filtr
    for(int i=0;i<A_supHFiltr.getOrigSetCR()().embDim();++i){
      if((unsigned int)A_supHFiltr.getOrigSetCR()().getPaddedWidth(i) + 4 >= CubeFaceIndexType::maxValAtCoord(i)){
*/
    for(int i=0;i<A_supHFiltr.getSetCR()().embDim();++i){
      if((unsigned int)A_supHFiltr.getSetCR()().getPaddedWidth(i) + 4 >= CubeFaceIndexType::maxValAtCoord(i)){
        string s="CrbIncHom: CubCellSet exceeds the maximum allowed size ";
        s << CubeFaceIndexType::maxValAtCoord(i) << " in direction " << i;
        throw s;
      }
    }
    // A shorthand for the vector (indexed by homology dimension) of vectors
    // (indexed by consecutive numbers) of chains forming the basis of homology of the subspace
    const std::vector<std::vector<ChainType> >& subBaseHomChain=A_subHFiltr.BaseHomologyChain();
    // A shorthand for the vector (indexed by homology dimension) of vectors
    // (indexed by consecutive numbers) of simplified (reduced) chains forming the basis
    // of homology of the superspace after all reductions (but not those for which Smith was needed, see below)
    const std::vector<std::vector<ChainType> >& supSimplifiedBaseHomChain=A_supHFiltr.SimplifiedBaseHomologyChain();
    // A shorthand to the quotient graded module of the part of homology of the reduced superset
    // which had to be treated by Smith algorithm (not reduced by coreduction algorithm or algebraic reductions algorithm)
    const QuotientGradedModule<FreeModuleType>& supFHM=A_supHFiltr.filteredHomModule();

    int topDimFromSmith=supFHM.TopDim();
    int topDimSimple=supSimplifiedBaseHomChain.size()-1;
    int topDim=std::max(topDimSimple,topDimFromSmith);

    // prepare the vector container for the matrices to be computed
    CRef<std::vector<MatrixType> > inclMatrixCR(new std::vector<MatrixType>()) ;
    // for every grade dimension
    for(int q=0;q<=topDim;++q){
      // this will be the number of columns in the matrix
      unsigned int n=subBaseHomChain[q].size();
      // this will be the number of rows in the matrix
      unsigned int m=supSimplifiedBaseHomChain[q].size();
      // prepare an uninitialized matrix
      inclMatrixCR().push_back(MatrixType(m,n));
      // for every basis vector in the homology of the subspace
      for(unsigned int j=0;j<n;++j){
        // c contains a working copy of the homology generator
        ChainType c(subBaseHomChain[q][j]);                         // a copy of the j-th base cycle in dim q of the subset
        A_supHFiltr.reduce(c);                                      // its reduction via the filter of the superset
        ColumnVectorType cVect;                                     // this will contain the vector of coefficients of the reduced c
                                                                    // in the basis of the chain group of the reduced superset
        ColumnVectorType cHomCoefVect;                              // this will contain the vector of coefficients of the
                                                                    // homolopgy class of the reduced c
                                                                    // in the basis of the homology of the reduced superset
        // i0 is the number of entries coming from Smith generators
        unsigned int i0=0;
        // first we insert entries from Smith generators
        if(q<=topDimFromSmith){
          i0=supFHM.component(q).numberOfGenerators();
          supFHM.component(q).BaseModulePtr()->coefVector(c,cVect);   // cVect stores the vector of coefficients
                                                                      // of the reduced chain c in the base of the chain group
          supFHM.component(q).coefVectorForCycle(cVect,cHomCoefVect); // the vector of coefficients of the homology of c
                                                                      // in the homology base of the reduced superset
          for(unsigned int i=0;i<i0;++i){
            inclMatrixCR()[q][i][j]=cHomCoefVect[i];                  // insert the respective coefficient
          }
        }
        // and here we insert entries from simple (non-Smith, obtained directly from reduction) generators
        if(q<=topDimSimple){
          for(unsigned int i=i0;i<m;++i){
            // The simple homology generators as chains have always exactly one non-trivial element
            // of the form (g,1), where g is the respective chain group generator
            // We insert c.at(g), where g==supSimplifiedBaseHomChain[q][i].begin()->first (the second element is one)
            inclMatrixCR()[q][i][j]=c.at(supSimplifiedBaseHomChain[q][i].begin()->first);
          }
        }
      }
    }
    return inclMatrixCR;
  }

  /* ------------------------  ------------------------ */
  // This is a modificiation of the above method designed specifically for the persistence code 07-12-2007
  // Not tested yet. Intended to save time on copying large matrices, because not matrices bur CRef's to
  // matrices will be transfered
/*
  static GradedCRefSparseIntMatrix CrbIncHom(
    const CubCellSetFiltrT<SCubCelSet,FreeChainComplexType>& A_subHFiltr,
    const CubCellSetFiltrT<SCubCelSet,FreeChainComplexType>& A_supHFiltr
  ){

    // *** Note: for the purposes of this method SparseIntMatrix is a vector of columns represented as sparse vectors
//    typedef std::vector<SparseIntVector> SparseIntMatrix;

    // A shorthand for the vector (indexed by homology dimension) of vectors
    // (indexed by consecutive numbers) of chains forming the basis of homology of the subspace
    const std::vector<std::vector<ChainType> >& subBaseHomChain=A_subHFiltr.BaseHomologyChain();
    // A shorthand for the vector (indexed by homology dimension) of vectors
    // (indexed by consecutive numbers) of simplified (reduced) chains forming the basis
    // of homology of the superspace after all reductions (but not those for which Smith was needed, see below)
    const std::vector<std::vector<ChainType> >& supSimplifiedBaseHomChain=A_supHFiltr.SimplifiedBaseHomologyChain();
    // A shorthand to the quotient graded module of the part of homology of the reduced superset
    // which had to be treated by Smith algorithm (not reduced by coreduction algorithm or algebraic reductions algorithm)
    const QuotientGradedModule<FreeModuleType>& supFHM=A_supHFiltr.filteredHomModule();

    int topDimFromSmith=supFHM.TopDim();
    int topDimSimple=supSimplifiedBaseHomChain.size()-1;
    int topDim=std::max(topDimSimple,topDimFromSmith);

    // prepare the vector container for the matrices to be computed
    GradedCRefSparseIntMatrix inclMatrixCRgraded;
    // for every grade dimension
    for(int q=0;q<=topDim;++q){
      // prepare an uninitialized matrix
      inclMatrixCRgraded.push_back(CRef<SparseIntMatrix>(new SparseIntMatrix()));
      // this will be the number of columns in the matrix
      unsigned int n=subBaseHomChain[q].size();
      // this will be the number of rows in the matrix
      unsigned int m=supSimplifiedBaseHomChain[q].size();
      // for every basis vector in the homology of the subspace
      for(unsigned int j=0;j<n;++j){
        inclMatrixCRgraded[q]().push_back(SparseIntVector());
        SparseIntVector& value=inclMatrixCRgraded[q]()[j];
        // c contains a working copy of the homology generator
        ChainType c(subBaseHomChain[q][j]);                         // a copy of the j-th base cycle in dim q of the subset
        A_supHFiltr.reduce(c);                                      // its reduction via the filter of the superset
        ColumnVectorType cVect;                                     // this will contain the vector of coefficients of the reduced c
                                                                    // in the basis of the chain group of the reduced superset
        ColumnVectorType cHomCoefVect;                              // this will contain the vector of coefficients of the
                                                                    // homolopgy class of the reduced c
                                                                    // in the basis of the homology of the reduced superset
        // i0 is the number of entries coming from Smith generators
        unsigned int i0=0;
        // first we insert entries from Smith generators
        if(q<=topDimFromSmith){
          i0=supFHM.component(q).numberOfGenerators();
          supFHM.component(q).BaseModulePtr()->coefVector(c,cVect);   // cVect stores the vector of coefficients
                                                                      // of the reduced chain c in the base of the chain group
          supFHM.component(q).coefVectorForCycle(cVect,cHomCoefVect); // the vector of coefficients of the homology of c
                                                                      // in the homology base of the reduced superset
          for(unsigned int i=0;i<i0;++i){
            if(cHomCoefVect[i]) value.at(i)=cHomCoefVect[i];          // insert the respective coefficient if nonzero
          }
        }
        // and here we insert entries from simple (non-Smith, obtained directly from reduction) generators
        if(q<=topDimSimple){
          for(unsigned int i=i0;i<m;++i){
            // The simple homology generators as chains have always exactly one non-trivial element
            // of the form (g,1), where g is the respective chain group generator
            // We insert c.at(g), where g==supSimplifiedBaseHomChain[q][i].begin()->first (the second element is one)
            int a=c.at(supSimplifiedBaseHomChain[q][i].begin()->first);
            if(a) value.at(i)=a;          // insert the respective coefficient if nonzero
          }
        }
      }
    }
    return inclMatrixCRgraded;
  }
*/

  /* ------------------------  ------------------------ */
  static std::string CrbIncHom(CRef<SCubCelSet> A_subCubCellSetCR,CRef<SCubCelSet> A_supCubCellSetCR){
    std::string result;
    Stopwatch swTot;
    CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> subHomFiltr(A_subCubCellSetCR);
    CubCellSetFiltrT<SCubCelSet,FreeChainComplexType> supHomFiltr(A_supCubCellSetCR);

    CRef<std::vector<MatrixType> > inclMatrixCR=CrbIncHom(subHomFiltr,supHomFiltr);


    result << "Homology of subset is: \n\n" << subHomFiltr  << "\n";
    result << "Homology of superset is: \n\n" << supHomFiltr  << "\n";
    result << "The matrix of inclusion map is: \n\n" << "\n";
    for(int q=0;q<=supHomFiltr.TopDim();++q){
      result << "  -- Dimension " << q << " -- " << "\n";
      result << inclMatrixCR()[q] << "\n";
    }
    result << "Computation completed in " << swTot  << "\n";
    return result;
  }


};// InclusionHomology

#endif //_INCLUSIONHOMOLOGY_H_
/// @}

