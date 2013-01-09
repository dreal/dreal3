/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file SubModule.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_SUBMODULE_H_)
#define _SUBMODULE_H_

#include "capd/homologicalAlgebra/ChainAux.hpp"

// ********** class SubModule ********** //
//   **** WARNING: This class uses unsafe pointers and can be safely used only with  ***
//   ***           the QuotientGradedModule class                                    ***
/*
  This class is a container for a submodule of a given free module.
  It stores a pointer to the base module and a matrix whose columns
  constitute a basis for the submodule.

  In the future, the pointer should be replaced by an intelligent pointer,
  which destructs the free modules it points to, when the module is no longer
  pointed at by any such pointers.

*/
template<typename freeModuleType>
class SubModule{
public:
  typedef typename freeModuleType::MatrixType MatrixType;
  SubModule():m_pBaseModule(0){}
  SubModule(
    const freeModuleType& A_BaseModule,
    MatrixType& A_matrix
  ):m_pBaseModule(&A_BaseModule){
    swap(A_matrix,m_baseChainMatrix);
  }
  friend void swap(SubModule& A_subm1,SubModule& A_subm2){
    std::swap(A_subm1.m_pBaseModule,A_subm2.m_pBaseModule);
    std::swap(A_subm1.m_baseChainMatrix,A_subm2.m_baseChainMatrix);
  }
  friend std::ostream& operator<<(std::ostream& out,const SubModule& A_SubM){
    if(A_SubM.m_pBaseModule) out << "Submodule of:" << *A_SubM.m_pBaseModule << std::endl;
    out << "   With generating chains: " << std::endl;
    std::vector<ChainAux<freeModuleType> > baseChain;
    matrixColumnsToChains(*A_SubM.m_pBaseModule,A_SubM.m_baseChainMatrix,baseChain);
    for(int i=0;i<(int)baseChain.size();++i){
      out << "g" << i << "=" << baseChain[i] << std::endl;
    }
    return out;
  }
  const MatrixType& baseChainMatrix()const{
    return m_baseChainMatrix;
  }
private:
  const freeModuleType* m_pBaseModule;
  MatrixType m_baseChainMatrix;
}; // ********** class SubModule ********** //

#endif //_SUBMODULE_H_
/// @}

