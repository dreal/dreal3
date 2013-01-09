/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file QuotientModule.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_QUOTIENTMODULE_H_)
#define _QUOTIENTMODULE_H_

#include "capd/homologicalAlgebra/FGAGrpSignature.h"
#include "capd/homologicalAlgebra/SubModule.h"

template<typename freeModuleType>
class QuotientModule;

template<typename freeModuleType>
void swap(QuotientModule<freeModuleType>& A_subm1,QuotientModule<freeModuleType>& A_subm2);

// ********** class QuotientModule ********** //
//   **** WARNING: This class uses unsafe pointers and can be safely used only with  ***
//   ***           the QuotientGradedModule class                                    ***
/*
  This class provides a container for a quotient module of two submodules
  of a given base module. The container is based on the presentation ot the quotient module
  as described in Theorem 3.58 of
    M. Mrozek, K. Mischaikow and T. Kaczynski,
    Computational Homology,
    Applied Mathematical Sciences 157, Springer-Verlag, New York, 2004
  It contains a pointer two the base module, the two submodules (dividend module and divisor module),
  the matrix containing in its columns the pseudo basis for the quotient module
  and a vector of orders of the pseudo basis elements

  The only non-default constructor takes as arguments a reference to the base module
  and two matrices containing bases of submodules as their columns. The construction then follows
  Algorithm 3.58 from the above book. However, most of the implementation is moved
  to the function quotientBaseMatrix from intMatrixAlgorithms package

*/
template<typename freeModuleType>
class QuotientModule{
public:
  typedef int IntType;
  typedef capd::vectalg::Matrix<IntType,0,0> IntMatrixType;
  typedef IntMatrixType::ColumnVectorType IntVectorType;

  typedef typename freeModuleType::MatrixType MatrixType;
  typedef typename freeModuleType::MatrixType::ColumnVectorType VectorType;
  typedef typename freeModuleType::MatrixType::ScalarType ScalarType;
  QuotientModule():m_pBaseModule(0),m_rank(0){}


  QuotientModule(
    const freeModuleType& A_BaseModule,
    typename freeModuleType::MatrixType& A_dividendModuleMatrix,
    typename freeModuleType::MatrixType& A_divisorModuleMatrix
  ):
    m_pBaseModule(&A_BaseModule),
    m_dividendModule(A_BaseModule,A_dividendModuleMatrix),
    m_divisorModule(A_BaseModule,A_divisorModuleMatrix)
  {
    // Compute the generators of quotient module by the method quotientBaseMatrix from intMatrixAlgorithms
    capd::matrixAlgorithms::quotientBaseMatrix(
      m_dividendModule.baseChainMatrix(),
      m_divisorModule.baseChainMatrix(),
      m_baseChainMatrix,
      m_baseChainOrder
    );
    m_rank=m_dividendModule.baseChainMatrix().numberOfColumns()-
           m_divisorModule.baseChainMatrix().numberOfColumns();
  }
  int rank() const{ return m_rank; }
  int numberOfGenerators() const{
    return m_baseChainMatrix.numberOfRows();
  }
  int numberOfTorsionElements() const{
    return m_baseChainOrder.dimension();
  }
  int generatorOrder(int i) const{
    return (
      i<m_baseChainOrder.dimension() ?
      m_baseChainOrder[i] :
      0
    );
  }
  bool torsionFree() const{ return m_baseChainOrder.dimension()==0;}

  std::string descriptor() const{
    std::ostringstream out;
    if(torsionFree()){
      if(rank()) out << "Z^" << rank();
      else out << "0";
    }else{
      if(rank()) out << "Z^" << rank() << " + ";
      for(int i=0;i<m_baseChainOrder.dimension();++i){
        out << "Z/" << m_baseChainOrder[i];
        if(i<m_baseChainOrder.dimension()-1) out << " + ";
      }
    };
    return out.str();
  }

  std::string torsionDescriptor() const{
    std::ostringstream out;
    for(int i=0;i<m_baseChainOrder.dimension();++i){
      out << "Z/" << m_baseChainOrder[i];
      if(i<m_baseChainOrder.dimension()-1) out << " + ";
    }
    return out.str();
  }

  std::vector<int> torsionVector() const{
    std::vector<int> v;
    for(int i=0;i<m_baseChainOrder.dimension();++i){
      v.push_back(m_baseChainOrder[i]);
    }
    return v;
  }

  const freeModuleType* BaseModulePtr() const{
    return m_pBaseModule;
  }

  operator FGAGrpSignature<ScalarType> (){
    std::vector<int> tv=torsionVector();
    return FGAGrpSignature<ScalarType> (m_rank,tv);
  }

  // Compute the vector of coefs in the base of a given cycle vector
  void coefVectorForCycle(const VectorType& A_cycleVector, VectorType& A_cycleCoefVector) const{
    solveLinearEquation(m_baseChainMatrix,A_cycleVector,A_cycleCoefVector);
  }

  template<typename freeModuleType2>
  friend void swap(QuotientModule<freeModuleType2>& A_subm1,QuotientModule<freeModuleType2>& A_subm2);

  friend std::ostream& operator<<(std::ostream& out,const QuotientModule& A_SubM){
    out << "Quotient Module" << std::endl;
    if(A_SubM.m_pBaseModule){
      out << "  Base Module is:" << *A_SubM.m_pBaseModule << std::endl;
      out << "  Dividend Module is:" << A_SubM.m_dividendModule << std::endl;
      out << "  Divisor Module is:" << A_SubM.m_divisorModule << std::endl;
    }
    out << "  +++ Generating chains in Quotient Group and their orders are: +++ " << std::endl;
    std::vector<ChainAux<freeModuleType> > baseChain;
    matrixColumnsToChains(*A_SubM.m_pBaseModule,A_SubM.m_baseChainMatrix,baseChain);
    for(int i=0;i<(int)baseChain.size();++i){
      out << "g" << i << "=" << baseChain[i] << " of order " << A_SubM.generatorOrder(i) << std::endl;
    }
    return out;
  }

  template<typename P_Chain>
  void exportBaseChains(
    std::vector<P_Chain>& A_chains,
    std::vector<IntType>& A_orders
  ) const{
    int m=m_baseChainMatrix.numberOfRows();
    int n=m_baseChainMatrix.numberOfColumns();
    A_chains.reserve(n);
    for(int j=0;j<n;++j){
      P_Chain c;
      for(int i=0;i<m;++i){
        if( m_baseChainMatrix[i][j] != ScalarType(0) ){
          c.insert(make_pair((*m_pBaseModule)[i],m_baseChainMatrix[i][j]));
        }
      }
      A_chains.push_back(c);
      A_orders.push_back(generatorOrder(j));
    }
  }  // ********** matrixColumnsToChains ********** //

private:
  const freeModuleType* m_pBaseModule;
  SubModule<freeModuleType> m_dividendModule;
  SubModule<freeModuleType> m_divisorModule;
  MatrixType m_baseChainMatrix;
  IntVectorType m_baseChainOrder; // only finite orders are stored here, inifinte orders, represented as 0 are returned by generatorOrder()
  int m_rank;
}; // ********** class QuotientModule ********** //

template<typename freeModuleType2>
inline void swap(QuotientModule<freeModuleType2>& A_subm1,QuotientModule<freeModuleType2>& A_subm2){
  std::swap(A_subm1.m_pBaseModule,A_subm2.m_pBaseModule);
  std::swap(A_subm1.m_dividendModule,A_subm2.m_dividendModule);
  std::swap(A_subm1.m_divisorModule,A_subm2.m_divisorModule);
  std::swap(A_subm1.m_baseChainMatrix,A_subm2.m_baseChainMatrix);
  std::swap(A_subm1.m_baseChainOrder,A_subm2.m_baseChainOrder);
  std::swap(A_subm1.m_rank,A_subm2.m_rank);
}

#endif //_QUOTIENTMODULE_H_
/// @}

