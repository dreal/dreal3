
/////////////////////////////////////////////////////////////////////////////
/// @file Pped2Set.hpp
/// @deprecated
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_PPED2SET_HPP_ 
#define _CAPD_DYNSET_PPED2SET_HPP_ 

#include "capd/dynset/Pped2Set.h"
#include "capd/vectalg/iobject.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
typename Pped2Set<MatrixType>::ScalarType Pped2Set<MatrixType>::size(void){
  return capd::vectalg::size( m_x + m_C*m_r0 + m_B*m_r );
}

template<typename MatrixType>
Pped2Set<MatrixType>::Pped2Set(const VectorType& the_x)
  : m_x(the_x),
    m_r(the_x.dimension()),
    m_r0(the_x.dimension()),
    m_B(MatrixType::Identity(the_x.dimension())),
    m_C(MatrixType::Identity(the_x.dimension())) {

  m_r.clear();
  split(m_x,m_r0);
}

template<typename MatrixType>
Pped2Set<MatrixType>::Pped2Set(const VectorType& the_x,const VectorType& the_r0)
  : m_x(the_x),
    m_r(the_x.dimension()),
    m_r0(the_r0),
    m_B(MatrixType::Identity(the_x.dimension())),
    m_C(MatrixType::Identity(the_x.dimension())) {

  m_r.clear();
  if(!subset(m_r,m_r0)) {
    m_x += m_r0;
    split(m_x,m_r0);
  }
}

template<typename MatrixType>
Pped2Set<MatrixType>::Pped2Set(int dim)
  : m_x(dim),
    m_r(dim),
    m_r0(dim),
    m_B(MatrixType::Identity(dim)),
    m_C(MatrixType::Identity(dim)) {

  m_x.clear();
  m_r.clear();
  m_r0.clear();
}

template<typename MatrixType>
void Pped2Set<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys) {
  move(dynsys,*this);
}

template<typename MatrixType>
void Pped2Set<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys, Pped2Set& result) const {

  MatrixType S(m_x.dimension(),m_x.dimension());

  VectorType xx = m_x + m_C*m_r0 + m_B*m_r;

  result.m_x = dynsys.Phi(m_x) + dynsys.Remainder(xx);
  MatrixType A = dynsys.JacPhi(xx);
  result.m_C = A*m_C;

  split(result.m_x,xx);
  split(result.m_C,S);
  xx += S*m_r0;
  result.m_B = A*m_B;
  split(result.m_B,S);
  result.m_r = m_r + capd::matrixAlgorithms::gauss(result.m_B,S*m_r+xx);
  if( &result!=this)
    result.m_r0 = m_r0;
}

template<typename MatrixType>
std::string Pped2Set<MatrixType>::show(void) const {

  std::ostringstream descriptor;
  descriptor << "PpedSet: x=";
  descriptor << m_x << "\n B=";
  descriptor << m_B << "\n r=";
  descriptor << m_r << "\n C=";
  descriptor << m_C << "\n r0=";
  descriptor << m_r0 << " ";
  return descriptor.str();
}

template<typename MatrixType>
typename Pped2Set<MatrixType>::VectorType Pped2Set<MatrixType>::affineTransformation(
    const MatrixType& A_M, const VectorType& A_C
  ) const {

  return A_M*(m_x-A_C) + (A_M*m_C)*m_r0 + (A_M*m_B)*m_r;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_PPED2SET_HPP_ 
