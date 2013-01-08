/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FreeModuleHomomorphism.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_FREEMODULEHOMOMORPHISM_H_)
#define _FREEMODULEHOMOMORPHISM_H_

// ********** class FreeModuleHomomorphism ********** //
/*
  This class provides a container for free module homomorphisms.
  It provides pointers to the domain and codomain and the matrix
  of the hommorphism in the bases of generators provided by domain
  and codomain.

  In the future, the pointers should be replaced by intelligent pointers,
  which destruct the free modules they point to, when the modules are no longer
  pointed at by any such pointers.
*/
template<typename generatorType,typename matrixType>
class FreeModuleHomomorphism{
public:
  FreeModuleHomomorphism():m_pDomain(0),m_pCodomain(0){}
  FreeModuleHomomorphism(
    const FreeModule<generatorType,matrixType>* A_pDomain,
    const FreeModule<generatorType,matrixType>* A_pCodomain,
    matrixType& A_coefMatrix
  ):m_pDomain(A_pDomain),m_pCodomain(A_pCodomain){
    std::swap(m_coefMatrix,A_coefMatrix);
  }
  friend void swap(FreeModuleHomomorphism& A_fmh1,FreeModuleHomomorphism& A_fmh2){
    std::swap(A_fmh1.m_pDomain,A_fmh2.m_pDomain);
    std::swap(A_fmh1.m_pCodomain,A_fmh2.m_pCodomain);
    std::swap(A_fmh1.m_coefMatrix,A_fmh2.m_coefMatrix);
  }
  const matrixType& coefMatrix() const{
    return m_coefMatrix;
  }
private:
  const FreeModule<generatorType,matrixType>* m_pDomain;
  const FreeModule<generatorType,matrixType>* m_pCodomain;
  matrixType m_coefMatrix;
}; // ********** class FreeModuleHomomorphism ********** //

#endif //_FREEMODULEHOMOMORPHISM_H_
/// @}

