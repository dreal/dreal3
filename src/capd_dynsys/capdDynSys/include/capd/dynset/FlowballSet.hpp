/////////////////////////////////////////////////////////////////////////////
/// @file FlowballSet.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_FLOWBALLSET_HPP_ 
#define _CAPD_DYNSET_FLOWBALLSET_HPP_ 

#include <stdexcept>
#include "capd/dynset/FlowballSet.h"
#include "capd/vectalg/Norm.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
typename FlowballSet<MatrixType>::ScalarType FlowballSet<MatrixType>::size(void)
{
  return capd::vectalg::size(intervalBall(m_x,m_r));
}

template<typename MatrixType>
FlowballSet<MatrixType>::FlowballSet(
    const typename FlowballSet<MatrixType>::VectorType& x,
    const typename FlowballSet<MatrixType>::ScalarType& r,
    const typename FlowballSet<MatrixType>::NormType& aNorm
  ) : m_x(x),m_r(r),m_n(aNorm.clone())
{}

template<typename MatrixType>
void FlowballSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType> &dynsys)
{
  if(dynsys.type() != "flow")
  {
    throw std::runtime_error("Attempt to use logarithmic norms with a cascade");
  }

/*   
  radius is multipled by the Lipschitz constant of the generator of DynSys
  on the interval enclosure of the ball. Note that the proper computation of Lipschitz
  for flows is hidden in the implementation of Lipschitz for flows (class odenum)
*/

  VectorType s(m_x.dimension()), vi(m_x.dimension());
  m_r *= dynsys.Lipschitz(vi = intervalBall(m_x,m_r),*m_n);

  VectorType y=dynsys.Phi(m_x);
  split(y,s);
  s += dynsys.Remainder(m_x);
  m_x = y;
  m_r += (*m_n)(s);
}

template<typename MatrixType>
void FlowballSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType> &dynsys, FlowballSet &result) const
{
  VectorType s(m_x.dimension()), vi(m_x.dimension());
  if(dynsys.type() != "flow")
  {
    throw std::runtime_error("Attempt to use logarithmic norms with a cascade");
  }

/*   
  radius is multipled by the Lipschitz constant of the generator of DynSys
  on the interval enclosure of the ball. Note that the proper computation of Lipschitz
  for flows is hidden in the implementation of Lipschitz for flows (class odenum)
*/

  result.m_r = m_r*dynsys.Lipschitz(vi = intervalBall(m_x,m_r),*m_n);

  VectorType y = dynsys.Phi(m_x);
  split(y,s);
  s += dynsys.Remainder(m_x);
  result.m_x = y;
  result.m_r += (*m_n)(s);
  delete result.m_n;
  result.m_n = m_n->clone();
}

template<typename MatrixType>
std::string FlowballSet<MatrixType>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << "FlowballSet(" << m_n->show() << "): x=";
  descriptor << m_x << " r=";
  descriptor << m_r << " ";
  return descriptor.str();
}

template<typename MatrixType>
typename FlowballSet<MatrixType>::VectorType FlowballSet<MatrixType>::affineTransformation(
    const MatrixType& A_M, const VectorType& A_C
  ) const
{
  return A_M*(intervalBall(m_x,m_r)-A_C);
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_FLOWBALLSET_HPP_ 
