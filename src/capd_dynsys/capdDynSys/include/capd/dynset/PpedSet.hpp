/////////////////////////////////////////////////////////////////////////////
/// @file PpedSet.hpp
/// @deprecated
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_PPEDSET_HPP_ 
#define _CAPD_DYNSET_PPEDSET_HPP_ 

#include "capd/dynset/PpedSet.h"
#include "capd/vectalg/iobject.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
PpedSet<MatrixType>::PpedSet(int dim)
  : m_x(dim),
    m_r(dim),
    m_B(MatrixType::Identity(dim)) {

  m_x.clear();
  m_r.clear();
}

template<typename MatrixType>
PpedSet<MatrixType>::PpedSet(const VectorType& x)
  : m_x(x),
    m_r(x.dimension()),
    m_B(MatrixType::Identity(x.dimension())) {

  split(m_x,m_r);
}

template<typename MatrixType>
PpedSet<MatrixType>::PpedSet(const VectorType& x,const VectorType& r)
  : m_x(x),
    m_r(r),
    m_B(MatrixType::Identity(x.dimension()))
{
  if( !subset(VectorType(x.dimension()),m_r) )
  {
    m_x+=m_r;
    split(m_x,m_r);
  }
}

template<typename MatrixType>
PpedSet<MatrixType>::PpedSet(
    const VectorType& x,
    const VectorType& r,
    const MatrixType& B
  ) : m_x(x),  m_r(r),  m_B(B) {

  if( !subset(VectorType(x.dimension()),m_r) ) {
    VectorType centerR = m_r;
    split(centerR,m_r);
    // m_x will be not a single point, but we must assure m_r contains zero
    m_x += m_B*centerR; 
  }
}

template<typename MatrixType>
typename PpedSet<MatrixType>::ScalarType PpedSet<MatrixType>::size(void) {
  return capd::vectalg::size(m_x + m_B*m_r);
}

template<typename MatrixType>
void PpedSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys) {
  move(dynsys,*this);
}

template<typename MatrixType>
void PpedSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys, PpedSet& result) const {

  MatrixType R(m_x.dimension(),m_x.dimension());

  VectorType xx = m_x + m_B*m_r;
  result.m_x = dynsys.Phi(m_x) + dynsys.Remainder(xx);
  result.m_B = dynsys.JacPhi(xx)*m_B;

  split(result.m_x,xx);
  split(result.m_B,R);
  result.m_r = m_r + capd::matrixAlgorithms::gauss(result.m_B,R*m_r+xx);
}

template<typename MatrixType>
std::string PpedSet<MatrixType>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << "PpedSet: x=";
  descriptor << m_x << "\n B=";
  descriptor << m_B << "\n r=";
  descriptor << m_r << " ";
  return descriptor.str();
}

template<typename MatrixType>
typename PpedSet<MatrixType>::VectorType PpedSet<MatrixType>::affineTransformation(
    const MatrixType& A_M, const VectorType& A_C
  ) const {

  return A_M*(m_x-A_C) + (A_M*m_B)*m_r;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_PPEDSET_HPP_ 
