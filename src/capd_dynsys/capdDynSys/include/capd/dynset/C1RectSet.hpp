
/////////////////////////////////////////////////////////////////////////////
/// @file C1RectSet.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C1RECTSET_HPP_
#define _CAPD_DYNSET_C1RECTSET_HPP_

#include <sstream>
#include "capd/dynset/C1RectSet.h"
#include "capd/auxil/minmax.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType, typename QRPolicy>
C1RectSet<MatrixType,QRPolicy>::C1RectSet(const NormType& aNorm, int dim)
  : C0BaseSet(dim),
    C1BaseSet(dim),
    m_Norm(aNorm.clone()) {
}

template<typename MatrixType, typename QRPolicy>
C1RectSet<MatrixType,QRPolicy>::C1RectSet(const C1RectSet& s)
  : C0BaseSet(s),
    C1BaseSet(s),
    m_Norm(s.m_Norm->clone())
{}

template<typename MatrixType, typename QRPolicy>
C1RectSet<MatrixType,QRPolicy>::C1RectSet(const VectorType& x, const NormType& aNorm)
  : C0BaseSet(x),
    C1BaseSet(x.dimension()),
    m_Norm(aNorm.clone()) {
}

template<typename MatrixType, typename QRPolicy>
C1RectSet<MatrixType,QRPolicy>::C1RectSet( const VectorType& x, const VectorType& r, const NormType& theNorm)
  : C0BaseSet(x,r),
    C1BaseSet(x.dimension()),
    m_Norm(theNorm.clone()) {
}


template<typename MatrixType, typename QRPolicy>
C1RectSet<MatrixType,QRPolicy>::C1RectSet(
    const VectorType& x,
    const MatrixType& B,
    const VectorType& r,
    const NormType& theNorm
  ):C0BaseSet(x, B, r),
    C1BaseSet(x.dimension()),
    m_Norm(theNorm.clone()) {
}

template<typename MatrixType, typename QRPolicy>
void C1RectSet<MatrixType,QRPolicy>::move(capd::dynsys::C1DynSys<MatrixType>& c1dynsys, C1RectSet& result) const {
  int dim = m_x.dimension();

  VectorType Rem(dim);
  MatrixType jacRem(dim,dim);

  VectorType xx = m_x + m_B*m_r;

  int found;
  VectorType z = c1dynsys.enclosure(xx,&found);
  MatrixType Z = c1dynsys.jacEnclosure(z,*m_Norm);
  c1dynsys.JacRemainder(z,Z,Rem,jacRem);

  MatrixType Jac = c1dynsys.JacPhi(xx);
  result.m_x = c1dynsys.Phi(m_x) + Rem;
// we use again z, the current value is unnecessary now
  split(result.m_x,z);

  Z = Jac*m_B;
  mid(Z,result.m_B);
  QRPolicy::orthonormalize(result.m_B,m_r);
  MatrixType Qtr = Transpose(result.m_B);
  result.m_r = (Qtr*Z)*m_r+Qtr*z;

// evaluation formula for C^1 part
// we evaluate the multiplication (Jac+jacRem)*(D+B*R)
  Jac += jacRem;

// we use jacRem again
  split(Jac,jacRem);

  result.m_D = Jac*m_D + jacRem*(m_D + m_Bjac * m_R);
  split(result.m_D,Z);
// we use jacRem again
  jacRem = Jac*m_Bjac;
  mid(jacRem,result.m_Bjac);
  QRPolicy::orthonormalize(result.m_Bjac);
  Qtr = Transpose(result.m_Bjac);
  result.m_R = (Qtr*jacRem)*m_R + Qtr*Z;
}

template<typename MatrixType, typename QRPolicy>
std::string C1RectSet<MatrixType,QRPolicy>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << name()
             << C0BaseSet::toString()
             << C1BaseSet::toString();
  return descriptor.str();
}


template<typename MatrixType, typename QRPolicy>
C1RectSet<MatrixType,QRPolicy> &C1RectSet<MatrixType,QRPolicy>::operator=(const VectorType& x)
{
  int dim = x.dimension();
  m_x = x;
  m_r = VectorType(dim);
  split(m_x,m_r);

  m_Bjac = m_D = m_B = MatrixType::Identity(dim);
  m_R = MatrixType(dim,dim);
  m_R.clear();

  return *this;
}

template<typename MatrixType, typename QRPolicy>
C1RectSet<MatrixType,QRPolicy>& C1RectSet<MatrixType,QRPolicy>::operator=(const C1RectSet& S)
{
  m_x = S.m_x;
  m_B = S.m_B;
  m_r = S.m_r;

  m_D = S.m_D;
  m_Bjac = S.m_Bjac;
  m_R = S.m_R;
  delete m_Norm;
  m_Norm = S.m_Norm->clone();
  return *this;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C1RECTSET_HPP_

