// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C1PpedSet.hpp
///
/// @author kapela
/// Created on: Oct 24, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_C1PPEDSET_HPP_
#define _CAPD_C1PPEDSET_HPP_


#include <sstream>
#include "capd/dynset/C1PpedSet.h"
#include "capd/capd/minmax.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
C1PpedSet<MatrixType>::C1PpedSet(const NormType& aNorm, int dim)
  : C0BaseSet(dim),
    C1BaseSet(dim),
    m_Norm(aNorm.clone()) {
}

template<typename MatrixType>
C1PpedSet<MatrixType>::C1PpedSet(const C1PpedSet<MatrixType>& s)
  : C0BaseSet(s),
    C1BaseSet(s),
    m_Norm(s.m_Norm->clone())
{}

template<typename MatrixType>
C1PpedSet<MatrixType>::C1PpedSet(const VectorType& x, const NormType& aNorm)
  : C0BaseSet(x),
    C1BaseSet(x.dimension()),
    m_Norm(aNorm.clone()) {
}

template<typename MatrixType>
C1PpedSet<MatrixType>::C1PpedSet( const VectorType& x, const VectorType& r, const NormType& theNorm)
  : C0BaseSet(x,r),
    C1BaseSet(x.dimension()),
    m_Norm(theNorm.clone()) {
}


template<typename MatrixType>
C1PpedSet<MatrixType>::C1PpedSet(
    const VectorType& x,
    const MatrixType& B,
    const VectorType& r,
    const NormType& theNorm
  ):C0BaseSet(x, B, r),
    C1BaseSet(x.dimension()),
    m_Norm(theNorm.clone()) {
}

template<typename MatrixType>
void C1PpedSet<MatrixType>::move(DynSysType & dynsys, C1PpedSet& result) const {

  int dim = m_x.dimension();
  VectorType Rem(dim);
  MatrixType jacRem(dim,dim);
  VectorType xx = m_x + m_B*m_r;

  VectorType z = dynsys.enclosure(xx);
  MatrixType Z = dynsys.jacEnclosure(z,*m_Norm);
  dynsys.JacRemainder(z,Z,Rem,jacRem);
  MatrixType Jac = dynsys.JacPhi(xx);

  result.m_x = dynsys.Phi(m_x) + Rem;
  result.m_B = dynsys.JacPhi(xx)*m_B;

  MatrixType R(dim,dim);
  split(result.m_x,z);
  split(result.m_B,R);
  result.m_r = m_r + capd::matrixAlgorithms::gauss(result.m_B,R*m_r+xx);


  Z = Jac*m_B;
  mid(Z,result.m_B);




  // evaluation formula for C^1 part
  // we evaluate the multiplication (Jac+jacRem)*(D+B*R)
  Jac += jacRem;

  // we use jacRem again
  split(Jac,jacRem);

  result.m_D = Jac*m_D + jacRem*(m_D + m_Bjac * m_R);
  split(result.m_D,Z);
  // we use jacRem again
  result.m_Bjac = Jac*m_Bjac;
  split(result.m_Bjac, jacRem);
  Z += jacRem*m_R;
  capd::matrixAlgorithms::gauss(result.m_Bjac, Z, jacRem);
  result.m_R = m_R + jacRem;
}

template<typename MatrixType>
std::string C1PpedSet<MatrixType>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << name()
             << C0BaseSet::toString()
             << C1BaseSet::toString();
  return descriptor.str();
}


template<typename MatrixType>
C1PpedSet<MatrixType> &C1PpedSet<MatrixType>::operator=(const VectorType& x)
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

template<typename MatrixType>
C1PpedSet<MatrixType>& C1PpedSet<MatrixType>::operator=(const C1PpedSet& S)
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

#endif // _CAPD_C1PPEDSET_HPP_

/// @}
