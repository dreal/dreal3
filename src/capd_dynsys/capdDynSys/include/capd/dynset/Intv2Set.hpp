/////////////////////////////////////////////////////////////////////////////
/// @file Intv2Set.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_INTV2SET_HPP_ 
#define _CAPD_DYNSET_INTV2SET_HPP_ 

#include "capd/dynset/Intv2Set.h"
#include "capd/vectalg/iobject.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
Intv2Set<MatrixType>::Intv2Set(const VectorType& x)
  : m_x(x),
    m_r(x.dimension()),
    m_r0(x.dimension()),
    m_C(MatrixType::Identity(x.dimension()))
{
  m_r.clear(); 
  split(m_x,m_r0);
}

template<typename MatrixType>
Intv2Set<MatrixType>::Intv2Set(int dim)
  : m_x(dim),
    m_r(dim),
    m_r0(dim),
    m_C(MatrixType::Identity(dim))
{
  m_x.clear();
  m_r.clear();
  m_r0.clear();
}

template<typename MatrixType>
Intv2Set<MatrixType>::Intv2Set(const VectorType& x, const VectorType& r0)
  : m_x(x),
    m_r(x.dimension()),
    m_r0(r0),
    m_C(MatrixType::Identity(x.dimension()))
{
  m_r.clear();
  if(!subset(m_r,m_r0))
  {
    m_x += m_r0;
    split(m_x,m_r0);
  }
}

template<typename MatrixType>
Intv2Set<MatrixType>::Intv2Set(const VectorType& x, const MatrixType& C, const VectorType& r0)
  : m_x(x),
    m_r(x.dimension()),
    m_r0(r0),
    m_C(C)
{
  m_r.clear();
  if(!subset(m_r,m_r0))
  {
    m_x += m_r0;
    split(m_x,m_r0);
  }
}

template<typename MatrixType>
typename Intv2Set<MatrixType>::ScalarType Intv2Set<MatrixType>::size(void)
{
  return capd::vectalg::size( m_x + m_C*m_r0 + m_r );
}

template<typename MatrixType>
void Intv2Set<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys)
{
  move(dynsys,*this);
}

template<typename MatrixType>
void Intv2Set<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys, Intv2Set& result) const
{
  MatrixType S(m_x.dimension(),m_x.dimension());

  VectorType xx = m_x + m_C*m_r0 + m_r;

  result.m_x = dynsys.Phi(m_x) + dynsys.Remainder(xx);
  MatrixType A = dynsys.JacPhi(xx);
  result.m_C = A*m_C;

  split(result.m_x,xx);
  split(result.m_C,S);
  result.m_r = xx + S*m_r0 + A*m_r;
  if( &result!=this )
    result.m_r0 = m_r0;
}

template<typename MatrixType>
std::string Intv2Set<MatrixType>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << "IntervalSet: x=";
  descriptor << m_x << "\n r=";
  descriptor << m_r << "\n C=";
  descriptor << m_C << "\n r0=";
  descriptor << m_r0 << " ";
  return descriptor.str();
}

template<typename MatrixType>
typename Intv2Set<MatrixType>::VectorType Intv2Set<MatrixType>::affineTransformation(
    const MatrixType& A_M, const VectorType& A_C
  ) const
{
  return A_M*(m_x+m_r-A_C) + (A_M*m_C)*m_r0;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_INTV2SET_HPP_ 
