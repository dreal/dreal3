/////////////////////////////////////////////////////////////////////////////
/// @file C0Rect2Set.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0RECT2SET_HPP_
#define _CAPD_DYNSET_C0RECT2SET_HPP_

#include <stdexcept>
#include "capd/vectalg/iobject.hpp"
#include "capd/dynset/C0Rect2Set.h"
#include "capd/geomset/CenteredDoubletonSet.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd {
namespace dynset {

template <typename MatrixType, typename QRPolicy>
void C0Rect2Set<MatrixType, QRPolicy>::move(DynSysType & dynsys) {
  move(dynsys, *this);
}

template <typename MatrixType, typename QRPolicy>
void C0Rect2Set<MatrixType, QRPolicy>::move(DynSysType & dynsys, C0Rect2Set<MatrixType, QRPolicy>& result) const {
  // important: here we assume that both m_r and m_r0 contains zero
  // this is assured by each contructor and each step of this algorithm

  MatrixType S(m_x.dimension(), m_x.dimension());
  VectorType y(m_x.dimension()), rem(m_x.dimension());
  MatrixType A(m_x.dimension(), m_x.dimension());

  VectorType xx = m_x + m_C * m_r0 + m_B * m_r;
  dynsys.encloseMap(m_x, xx, y, A, rem);

  result.m_x = y + rem;
  result.m_C = A * m_C;
  // xx is unnecessary now
  split(result.m_x, xx);
  split(result.m_C, S);
  xx += S * m_r0;
  // S is unnecessary now, so we can use it again
  S = A * m_B;

  mid(S, result.m_B); // the same as result.m_B = midMatrix(S), but faster
  try {
    QRPolicy::orthonormalize(result.m_B, m_r);
  } catch(...) {
    result.m_B = MatrixType::Identity(m_x.dimension());
  }
  MatrixType Qtr = Transpose(result.m_B);

  result.m_r = (Qtr * S) * m_r + Qtr * xx;
  if(&result != this)
    result.m_r0 = m_r0;

}

template <typename MatrixType, typename QRPolicy>
std::string C0Rect2Set<MatrixType, QRPolicy>::show(void) const {
  std::ostringstream descriptor;
  descriptor << "C0Rect2Set:\n" << BaseSet::toString();
  return descriptor.str();
}

}
} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0RECT2SET_HPP_
