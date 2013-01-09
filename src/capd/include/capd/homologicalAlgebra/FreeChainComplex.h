/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FreeChainComplex.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_FREECHAINCOMPLEX_H_)
#define _FREECHAINCOMPLEX_H_

#include "capd/homologicalAlgebra/FreeModuleHomomorphism.h"

template<typename freeModuleType>
class FreeChainComplex;

template<typename freeModuleType>
std::ostream& operator<<(std::ostream& out,const FreeChainComplex<freeModuleType>&);

template<typename freeModuleType>
void swap(FreeChainComplex<freeModuleType>& A_fcc1,FreeChainComplex<freeModuleType>&);

/*
template<typename freeModuleType, typename P_GeneratorCode, int P_storeReducedPairs>
class ReducibleFreeChainComplex;
*/

// ********** class FreeChainComplex ********** //
/*
  This class is used to store a free, finitely generated chain complex.
  This is not a dynamic structure as ReducibleFreeChainComplex.
  Its objects are not allowed to change, once constructed.

  The class stores a vector of free modules and a vector of boundary homomorphisms
  for the interval of grades, where the modules are non trivial.

  The two constructors implemented in FreeChainComplex.hpp
  are described in detail there
*/
template<typename freeModuleType>
class FreeChainComplex{
public:
  typedef freeModuleType FreeModuleType;
  typedef typename freeModuleType::MatrixType MatrixType;
  typedef typename freeModuleType::GeneratorType GeneratorType;

  FreeChainComplex(){}
  // construct a free chain complex from a std::vector of generators - see FreeChainComplex.hpp
  // needed only in some conretizations, so changed to template to avoid forced compilation
  template<typename GeneratorType2>
  FreeChainComplex(const std::vector<GeneratorType2>& A_gens);
  // construct a free chain complex from a std::set of generators - see FreeChainComplex.hpp
  // needed only in some conretizations, so changed to template to avoid forced compilation
  template<typename GeneratorType2>
  FreeChainComplex(const std::set<GeneratorType2>& A_gensSet);

  const freeModuleType& chainModule(int i) const{
    return m_chainModule[i];
  }
  const FreeModuleHomomorphism<GeneratorType,MatrixType>& boundaryHomomorphism(int i) const{
    return m_boundaryHomomorphism[i];
  }
  int topDim() const{
    return m_topDim;
  }
  int numberOfGenerators() const{
    int s=0;
    for(int i=0;i<=m_topDim;++i) s+=m_chainModule[i].numberOfGenerators();
    return s;
  }
  friend void swap<freeModuleType>(FreeChainComplex<freeModuleType>& A_fcc1,FreeChainComplex<freeModuleType>& A_fcc2);
  friend std::ostream& operator<< <freeModuleType>(std::ostream& out, const FreeChainComplex& A_fCC);


  template<typename freeModuleType2,typename GeneratorCode>
  friend class ReducibleFreeChainComplex;

private:
  int m_topDim;
  std::vector<FreeModule<GeneratorType,MatrixType> > m_chainModule;
  std::vector< FreeModuleHomomorphism<GeneratorType,MatrixType> > m_boundaryHomomorphism;
}; // ********** class FreeChainComplex ********** //

// ++++++++++++++++++++++++++++ inline functions definitions +++++++++++++++++++++++++++++++++++ //

template<typename freeModuleType>
inline void swap(FreeChainComplex<freeModuleType>& A_fcc1,FreeChainComplex<freeModuleType>& A_fcc2){
  std::swap(A_fcc1.m_topDim,A_fcc2.m_topDim);
  std::swap(A_fcc1.m_chainModule,A_fcc2.m_chainModule);
  std::swap(A_fcc1.m_boundaryHomomorphism,A_fcc2.m_boundaryHomomorphism);
}


#endif //_FREECHAINCOMPLEX_H_
/// @}

