/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file IntvSet.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_INTVSET_HPP_ 
#define _CAPD_DYNSET_INTVSET_HPP_ 

#include "capd/dynset/IntervalSet.h"
#include "capd/vectalg/iobject.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

// move  by  Jac*x + remainder
namespace capd{
namespace dynset{

template<typename MatrixType>
IntervalSet<MatrixType>::IntervalSet(void)
{
  m_x.clear(); m_r.clear();
}

template<typename MatrixType>
IntervalSet<MatrixType>::IntervalSet(int dim)
  : m_x(dim), m_r(dim)
{
  m_x.clear(); m_r.clear();
}

template<typename MatrixType>
IntervalSet<MatrixType>::IntervalSet(const VectorType& x)
  : m_x(x), m_r(x.dimension())
{
  m_r.clear();
}

template<typename MatrixType>
IntervalSet<MatrixType>::IntervalSet(const VectorType& x, const VectorType& r)
  : m_x(x), m_r(r)
{
  if(!subset(VectorType(x.dimension()),m_r))
  {
    m_x += m_r;
    split(m_x,m_r);
  }
}


template<typename MatrixType>
typename IntervalSet<MatrixType>::ScalarType IntervalSet<MatrixType>::size(void)
{
  return capd::vectalg::size(m_x+m_r);
}

template<typename MatrixType>
void IntervalSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys)
{
  VectorType xx = m_x+m_r;
  m_x = dynsys.Phi(m_x) + dynsys.JacPhi(xx)*m_r + dynsys.Remainder(xx);
  split(m_x,m_r);
}

template<typename MatrixType>
void IntervalSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys, IntervalSet& result) const
{
  VectorType xx = m_x + m_r;
  result.m_x = dynsys.Phi(m_x) + dynsys.JacPhi(xx)*m_r + dynsys.Remainder(xx);
  split(result.m_x,result.m_r);
}

template<typename MatrixType>
std::string IntervalSet<MatrixType>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << "IntervalSet: x=";
  descriptor << m_x << " r=";
  descriptor << m_r << " ";
  return descriptor.str();
}

template<typename MatrixType>
typename IntervalSet<MatrixType>::VectorType IntervalSet<MatrixType>::affineTransformation(
    const MatrixType& A_M, const VectorType& A_C
  ) const
{
  return A_M*(m_x+m_r-A_C);
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_INTVSET_HPP_ 

/// @}
