/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file QuotientGradedModule.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_QUOTIENTGRADEDMODULE_H_)
#define _QUOTIENTGRADEDMODULE_H_

#include "capd/homologicalAlgebra/HomologySignature.h"
#include "capd/homologicalAlgebra/QuotientModule.h"
#include "capd/auxil/CRef.h"

template<typename freeModuleType>
class QuotientGradedModule;

template<typename freeModuleType2>
void swap(QuotientGradedModule<freeModuleType2>& A_qgm1,QuotientGradedModule<freeModuleType2>& A_qgm2);

// ********** class QuotientGradedModule ********** //
/*
  This class provides a container to store homology (the results of homology computations),
  which consists of a graded module of quotient modules.
*/
template<typename freeModuleType>
class QuotientGradedModule{
public:
  typedef typename freeModuleType::MatrixType MatrixType;
  typedef typename freeModuleType::GeneratorType GeneratorType;
  typedef typename freeModuleType::MatrixType::ScalarType ScalarType;

  QuotientGradedModule():m_topDim(-1){}

  QuotientGradedModule(
    std::vector<QuotientModule<freeModuleType> >& A_quotientModuleVector,
    const CRef<FreeChainComplex<freeModuleType> >& A_masterChainComplexCR
  ):
    m_topDim(A_quotientModuleVector.size()-1),
    m_masterChainComplexCR(A_masterChainComplexCR)
  {
    swap(A_quotientModuleVector,m_componentModule);
  }

  template<typename freeModuleType2>
  friend void swap(QuotientGradedModule<freeModuleType2>& A_qgm1,QuotientGradedModule<freeModuleType2>& A_qgm2);

  friend std::ostream& operator<<(std::ostream& out, const QuotientGradedModule& A_qgM){
    out << "--- Quotient Graded Module ---" << std::endl;
    for(int i=0;i<A_qgM.m_topDim+1;++i){
      out << "  Dimension " << i << std::endl;
      out << A_qgM.m_componentModule[i] << std::endl;
    }
    return out;
  }

  operator CRef<HomologySignature<ScalarType> >(){
    CRef<HomologySignature<ScalarType> > hsCR(new HomologySignature<ScalarType> ());
    for(unsigned int i=0;i<m_componentModule.size();++i) hsCR().push_back(FGAGrpSignature<ScalarType> (m_componentModule[i]));
    return hsCR;
  }

  std::string descriptor() const{
    std::ostringstream out;
    for(int i=0;i<m_topDim+1;++i){
      out << "H_" << i << " = " << m_componentModule[i].descriptor() << std::endl;
    }
    return out.str();
  }

  const QuotientModule<freeModuleType>& component(int i) const{
    return m_componentModule[i];
  }

  int TopDim() const{
    return m_topDim;
  }

private:
  int m_topDim;
  CRef<FreeChainComplex<freeModuleType> > m_masterChainComplexCR;
  std::vector<QuotientModule<freeModuleType> > m_componentModule;
}; // ********** class QuotientGradedModule ********** //

template<typename freeModuleType2>
inline void swap(QuotientGradedModule<freeModuleType2>& A_qgm1,QuotientGradedModule<freeModuleType2>& A_qgm2){
  std::swap(A_qgm1.m_topDim,A_qgm2.m_topDim);
  std::swap(A_qgm1.m_componentModule,A_qgm2.m_componentModule);
}

#endif //_QUOTIENTGRADEDMODULE_H_
/// @}

