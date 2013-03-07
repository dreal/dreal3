/////////////////////////////////////////////////////////////////////////////
/// @file C0PpedQSet.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0RECTSETQ_HPP_
#define _CAPD_DYNSET_C0RECTSETQ_HPP_

#include "capd/vectalg/iobject.hpp"
#include "capd/dynset/C0PpedQSet.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"


namespace capd{
namespace dynset{

template<typename MatrixType, typename QRPolicy>
void C0PpedQSet<MatrixType,QRPolicy>::move(DynSysType & dynsys) {
  move(dynsys,*this);
}

template<typename MatrixType, typename QRPolicy>
void C0PpedQSet<MatrixType,QRPolicy>::move(DynSysType & dynsys, C0PpedQSet& result) const {

  VectorType y(m_x.dimension()),       // Phi(m_x)
             rem(m_x.dimension());     // remainder of numerical method (error)
  MatrixType A(m_x.dimension(), m_x.dimension());  // Jacobian of Phi computed on xx

  VectorType xx = m_x + m_B * m_r;      // bounds for current set
  dynsys.encloseMap(m_x, xx, y, A, rem);

  result.m_x = y + rem;
  MatrixType D = A*m_B;
// xx is unnecessary, we can use it again
  split(result.m_x,xx);
  mid(D,result.m_B);
  QRPolicy::orthonormalize(result.m_B, m_r, this->level);
  MatrixType Q_1 = QRPolicy::invertMatrix(result.m_B);
  result.m_r = (Q_1*D)*m_r + Q_1*xx;
}

template<typename MatrixType, typename QRPolicy>
std::string C0PpedQSet<MatrixType,QRPolicy>::show(void) const
{
  //std::ostringstream descriptor;
  //descriptor << "C0PpedQSet:\n" << toString();
  //return descriptor.str();
  return "C0PpedQSet:\n" + BaseSet::toString();
}


}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0RECTSETQ_HPP_


















