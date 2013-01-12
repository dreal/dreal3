////////////////////////////////////////////////////////////////////////////
/// @file C1Pped2Set.hpp
///
/// @author kapela
/// Created on: Oct 25, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C1PPED2SET_HPP_
#define _CAPD_DYNSET_C1PPED2SET_HPP_


#include <sstream>
#include "capd/auxil/minmax.h"
#include "capd/dynset/C1Pped2Set.h"
#include "capd/geomset/CenteredDoubletonSet.hpp"
#include "capd/geomset/MatrixDoubletonSet.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
C1Pped2Set<MatrixType>::C1Pped2Set(const NormType& aNorm, int dim)
  : C0BaseSet(dim),
    C1BaseSet(dim),
    m_currentSet(dim),
    m_currentMatrix(MatrixType::Identity(dim)),
    m_Norm(aNorm.clone()){
}


template<typename MatrixType>
C1Pped2Set<MatrixType>::C1Pped2Set(const C1Pped2Set& s)
  : C0BaseSet(s),
    C1BaseSet(s),
    m_currentSet(s.m_currentSet),
    m_currentMatrix(s.m_currentMatrix),
    m_Norm(s.m_Norm->clone()){
}

template<typename MatrixType>
C1Pped2Set<MatrixType>::C1Pped2Set(const VectorType& x, const NormType& aNorm)
 : C0BaseSet(x),
   C1BaseSet(x.dimension()),
   m_currentSet(x),
   m_currentMatrix(MatrixType::Identity(x.dimension())),
   m_Norm(aNorm.clone()){
}

template<typename MatrixType>
C1Pped2Set<MatrixType>::C1Pped2Set(
  const VectorType& x,
  const VectorType& r0,
  const NormType& aNorm
  ) : C0BaseSet(x, r0),
  C1BaseSet(x.dimension()),
  m_currentSet(x+r0),
  m_currentMatrix(MatrixType::Identity(x.dimension())),
  m_Norm(aNorm.clone()){
}

template<typename MatrixType>
C1Pped2Set<MatrixType>::C1Pped2Set(
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

//-----------------------------------------------

template<typename MatrixType>
void C1Pped2Set<MatrixType>::move(DynSysType &c1dynsys, C1Pped2Set &result) const
{
  int dim = m_x.dimension();
  VectorType Rem(dim);
  MatrixType jacRem(dim,dim);

  VectorType xx = m_currentSet;

  int found;
  VectorType Enc = c1dynsys.enclosure(xx,&found);
  MatrixType S = c1dynsys.jacEnclosure(Enc,*m_Norm);
  c1dynsys.JacRemainder(Enc,S,Rem,jacRem);
  MatrixType Jac = c1dynsys.JacPhi(xx);

  result.m_x = c1dynsys.Phi(m_x) + Rem;
  result.m_C = Jac*m_C;
  MatrixType A = Jac*m_B;
  result.m_currentSet = result.m_x + result.m_C*m_r0 + A*m_r;

// xx is unnecesarry now
  capd::vectalg::split(result.m_x,xx);
  capd::vectalg::split(result.m_C,S);
  xx += S*m_r0;
// S is unnecessary now
  capd::vectalg::mid(A,result.m_B); // result.m_B = midMatrix(A) but faster
  capd::matrixAlgorithms::orthonormalize(result.m_B,m_r);
  MatrixType Qtr = Transpose(result.m_B);
  result.m_r = (Qtr*A)*m_r + Qtr*xx;


//-----------------------------------------------

  Jac += jacRem;
  result.m_D = Jac*m_D;
  result.m_Cjac = Jac * m_Cjac;
  MatrixType X = Jac*m_Bjac;
  result.m_currentMatrix = result.m_D + result.m_Cjac*m_R0 + X*m_R;
  split(result.m_Cjac,S);
  result.m_D +=  S*m_R0;

  split(result.m_D,S);

  // S is unnecessary now, so we will use it again
  mid(X,result.m_Bjac);
  capd::matrixAlgorithms::orthonormalize(result.m_Bjac);
  Qtr = Transpose(result.m_Bjac);
  result.m_R = (Qtr*X)*m_R + Qtr*S;

  if (&result!=this){
    result.m_r0 = m_r0;
    result.m_R0 = m_R0;
  }


}

// ------------------------------------------------------------------------

template<typename MatrixType>
std::string C1Pped2Set<MatrixType>::show(void) const {
  std::ostringstream descriptor;
  descriptor << name()
             << C0BaseSet::toString()
             << C1BaseSet::toString();
  return descriptor.str();
}

template<typename MatrixT>
C1Pped2Set<MatrixT>::operator typename C1Pped2Set<MatrixT>::MatrixType() const {
  return m_currentMatrix;
}

template<typename MatrixType>
C1Pped2Set<MatrixType> &C1Pped2Set<MatrixType>::operator=(const VectorType &x)
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

template<typename MatrixType>
C1Pped2Set<MatrixType>& C1Pped2Set<MatrixType>::operator=(const C1Pped2Set &S)
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
#endif // _CAPD_C1PPED2SET_HPP_

