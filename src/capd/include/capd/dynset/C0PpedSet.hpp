/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C0PpedSet.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0PPEDSET_HPP_
#define _CAPD_DYNSET_C0PPEDSET_HPP_

#include "capd/dynset/C0PpedSet.h"
#include "capd/vectalg/iobject.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
void C0PpedSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys) {
  move(dynsys,*this);
}

template<typename MatrixType>
void C0PpedSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType>& dynsys, C0PpedSet& result) const {
  MatrixType R(m_x.dimension(),m_x.dimension());

  VectorType xx = m_x + m_B*m_r;
  result.m_x = dynsys.Phi(m_x) + dynsys.Remainder(xx);
  result.m_B = dynsys.JacPhi(xx)*m_B;

  split(result.m_x,xx);
  split(result.m_B,R);
  result.m_r = m_r + capd::matrixAlgorithms::gauss(result.m_B,R*m_r+xx);
}


template<typename MatrixType>
std::string C0PpedSet<MatrixType>::show(void) const {
  std::ostringstream descriptor;
  descriptor << "C0PpedSet:\n" << BaseSet::toString();
  return descriptor.str();
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0PPEDSET_HPP_

/// @}
