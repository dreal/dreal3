/////////////////////////////////////////////////////////////////////////////
/// @file C1Rect2Set.hpp
///
/// @author kapela
/// Created on: Oct 25, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C1RECT2SET_HPP_
#define _CAPD_DYNSET_C1RECT2SET_HPP_


#include <sstream>
#include "capd/auxil/minmax.h"
#include "capd/dynset/C1Rect2Set.h"
#include "capd/geomset/CenteredDoubletonSet.hpp"
#include "capd/geomset/MatrixDoubletonSet.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"
#include "capd/dynset/QRPolicy.h"

namespace capd{
namespace dynset{

template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy>::C1Rect2Set(const NormType& aNorm, int dim)
  : C0BaseSet(dim),
    C1BaseSet(dim),
    m_currentSet(dim),
    m_currentMatrix(MatrixType::Identity(dim)),
    m_Norm(aNorm.clone()){
}


template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy>::C1Rect2Set(const C1Rect2Set& s)
  : C0BaseSet(s),
    C1BaseSet(s),
    m_currentSet(s.m_currentSet),
    m_currentMatrix(s.m_currentMatrix),
    m_Norm(s.m_Norm->clone()){
}

template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy>::C1Rect2Set(const VectorType& x, const NormType& aNorm)
 : C0BaseSet(x),
   C1BaseSet(x.dimension()),
   m_currentSet(x),
   m_currentMatrix(MatrixType::Identity(x.dimension())),
   m_Norm(aNorm.clone()){
}

template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy>::C1Rect2Set(
  const VectorType& x,
  const VectorType& r0,
  const NormType& aNorm
  ) : C0BaseSet(x, r0),
  C1BaseSet(x.dimension()),
  m_currentSet(x+r0),
  m_currentMatrix(MatrixType::Identity(x.dimension())),
  m_Norm(aNorm.clone()){
}

template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy>::C1Rect2Set(
  const VectorType& x,
  const MatrixType& C,
  const VectorType& r0,
  const NormType& aNorm
  ): C0BaseSet(x, C, r0),
  C1BaseSet(x.dimension()),
  m_currentSet(x + C * r0),
  m_currentMatrix(MatrixType::Identity(x.dimension())),
  m_Norm(aNorm.clone()){
}

template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy>::C1Rect2Set(
  const C0BaseSet & c0part,
  const C1BaseSet & c1part,
  const NormType & norm
  ) : C0BaseSet(c0part),
  C1BaseSet(c1part),
  m_currentSet(VectorType(c0part)),
  m_currentMatrix(MatrixType(c1part)),
  m_Norm(norm.clone()){
}

//-----------------------------------------------

template<typename MatrixType, typename QRPolicy>
void C1Rect2Set<MatrixType,QRPolicy>::move(capd::dynsys::C1DynSys<MatrixType> &c1dynsys, C1Rect2Set &result) const
{
  int dim = m_x.dimension();
  VectorType rem(dim), phi(dim);
  MatrixType jacRem(dim,dim), jacPhi(dim,dim), S(dim,dim);

  VectorType xx = m_currentSet;
  c1dynsys.encloseMap(m_x,xx,phi,jacPhi,rem,jacRem,*m_Norm);

  result.m_x = phi + rem;
  result.m_C = jacPhi*m_C;
  MatrixType A = jacPhi*m_B;
  result.m_currentSet = result.m_x + result.m_C*m_r0 + A*m_r;

// xx is unnecesarry now
  capd::vectalg::split(result.m_x,xx);
  capd::vectalg::split(result.m_C,S);
  xx += S*m_r0;
// S is unnecessary now
  capd::vectalg::mid(A,result.m_B); // result.m_B = midMatrix(A) but faster
  try{
    QRPolicy::orthonormalize(result.m_B,m_r);
  }catch(...)
  {
    result.m_B = MatrixType::Identity(m_x.dimension());
  }
  MatrixType Qtr = Transpose(result.m_B);
  result.m_r = (Qtr*A)*m_r + Qtr*xx;


//-----------------------------------------------

  jacPhi += jacRem;
  result.m_D = jacPhi*m_D;
  result.m_Cjac = jacPhi * m_Cjac;
  MatrixType X = jacPhi * m_Bjac;
  result.m_currentMatrix = result.m_D + result.m_Cjac*m_R0 + X*m_R;
  split(result.m_Cjac,S);
  result.m_D +=  S*m_R0;

  split(result.m_D,S);

  // S is unnecessary now, so we will use it again
  mid(X,result.m_Bjac);
  QRPolicy::orthonormalize(result.m_Bjac);
  Qtr = Transpose(result.m_Bjac);
  result.m_R = (Qtr*X)*m_R + Qtr*S;

  if (&result!=this){
    result.m_R0 = m_R0;
    result.m_r0 = m_r0;
  }

}

// ------------------------------------------------------------------------

template<typename MatrixType, typename QRPolicy>
std::string C1Rect2Set<MatrixType,QRPolicy>::show(void) const {
  std::ostringstream descriptor;
  descriptor << name()
             << C0BaseSet::toString()
             << C1BaseSet::toString();
  return descriptor.str();
}

template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy>::operator typename C1Rect2Set<MatrixType,QRPolicy>::MatrixType() const {
  return m_currentMatrix;
}

template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy> &C1Rect2Set<MatrixType,QRPolicy>::operator=(const VectorType &x)
{

  C0BaseSet::operator=(x);
  int dim = x.dimension();
  m_currentMatrix = m_Bjac = m_Cjac = m_D = MatrixType::Identity(dim);
  m_R = MatrixType(dim,dim);
  m_R.clear();
  m_R0 = MatrixType(dim,dim);
  m_R0.clear();

  return *this;
}

template<typename MatrixType, typename QRPolicy>
C1Rect2Set<MatrixType,QRPolicy>& C1Rect2Set<MatrixType,QRPolicy>::operator=(const C1Rect2Set &S)
{
  if(&S==this)
    return *this;
  m_x = S.m_x;
  m_B = S.m_B;
  m_r = S.m_r;
  m_C = S.m_C;
  m_r0 = S.m_r0;

  m_D = S.m_D;
  m_Bjac = S.m_Bjac;
  m_R = S.m_R;
  m_Cjac = S.m_Cjac;
  m_R0 = S.m_R0;
  m_currentSet = S.m_currentSet;
  m_currentMatrix = S.m_currentMatrix;

  delete m_Norm;
  m_Norm = S.m_Norm->clone();
  return *this;
}

}} // namespace capd::dynset
#endif // _CAPD_C1RECT2SET_HPP_
