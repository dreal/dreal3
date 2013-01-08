/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file IC1Rect2.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_IC1RECT2_H_
#define _CAPD_IC1RECT2_H_

#include "capd/dynset/C1Set.h"
#include "capd/vectalg/Norm.h"
#include "capd/dynset/C1Rect2.hpp"
#include "capd/IMatrix.h"
#include "capd/vectalg/iobject.hpp"

template class capd::dynset::C1Rect2<capd::IMatrix>;
/* C^1-Lohner algorithm.
   Derivative of the flow moved via QR decomposition (third method)
   the set part - QR decomposition (3-rd method)
*/

namespace capd{

class IC1Rect2 : public capd::dynset::C1Set<IMatrix>{
public:
  typedef IMatrix MatrixType;
  typedef IVector VectorType;
  typedef DInterval ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::dynset::C1Rect2<IMatrix> BaseSet;
  typedef BaseSet::SetType SetType;
  typedef BaseSet::DynSysType DynSysType;

  IC1Rect2(const NormType& norm, int d)
    : m_set(norm,d)
  {}
  IC1Rect2(const VectorType& x, const NormType& norm, double sFactor = 20)
    : m_set(x,norm,sFactor)
  {}

  IC1Rect2(const VectorType& x, const VectorType& r, const NormType& norm, double sFactor = 20)
    : m_set(x,r,norm,sFactor)
  {}
  IC1Rect2(const VectorType& x, const MatrixType& C, const VectorType& r, const NormType& norm, double sFactor = 20)
    : m_set(x,C,r,norm,sFactor)
  {}
  
   void move(DynSysType & c1dynsys){
    m_set.move(c1dynsys);
  }
  void move(DynSysType & c1dynsys, IC1Rect2& result) const{
    m_set.move(c1dynsys,result.m_set);
  }

  std::string show(void) const{
    return m_set.show();
  }
  const NormType* getNorm(void) const{
    return m_set.getNorm();
  }
  void setFactor(double sFactor){
    m_set.setFactor(sFactor);
  }
  void disableSwapping(){
    m_set.disableSwapping();
  }
  double getFactor(){
    return m_set.getFactor();
  }

  operator VectorType() const{
    return VectorType(m_set);
  }
  operator MatrixType() const{
    return MatrixType(m_set);
  }

  IC1Rect2 &operator=(const IC1Rect2 &S){
    m_set = S.m_set;
    return *this;
  }
  
private:
  BaseSet m_set;
};

} // the end of the namespace capd

#endif // _CAPD_IC1RECT2_H_

/// @}
