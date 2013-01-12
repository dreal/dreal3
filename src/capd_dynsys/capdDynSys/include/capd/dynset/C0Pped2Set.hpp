/////////////////////////////////////////////////////////////////////////////
/// @file C0Pped2Set.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0PPED2SET_HPP_
#define _CAPD_DYNSET_C0PPED2SET_HPP_

#include "capd/dynset/C0Pped2Set.h"
#include "capd/vectalg/iobject.hpp"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"
#include "capd/geomset/CenteredDoubletonSet.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
void C0Pped2Set<MatrixType>::move(DynSysType & dynsys){
  move(dynsys,*this);
}

template<typename MatrixType>
void C0Pped2Set<MatrixType>::move(DynSysType & dynsys,
                                C0Pped2Set& result) const {
  VectorType y(m_x.dimension()), rem(m_x.dimension());
  MatrixType A(m_x.dimension(), m_x.dimension());

  VectorType xx = m_x + m_C * m_r0 + m_B * m_r;
  dynsys.encloseMap(m_x, xx, y, A, rem);

  result.m_x = y + rem;
  result.m_C = A * m_C;
  result.m_B = A * m_B;

  // A is unnecessary now
  split(result.m_x,xx);
  split(result.m_C,A);
  xx += A*m_r0;
  split(result.m_B,A);
  result.m_r = m_r + capd::matrixAlgorithms::gauss(result.m_B,A*m_r+xx);
  if( &result!=this)
    result.m_r0 = m_r0;
}

template<typename MatrixType>
std::string C0Pped2Set<MatrixType>::show(void) const {
  std::ostringstream descriptor;
  descriptor << "C0Pped2Set:\n" << BaseSet::toString();
  return descriptor.str();
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0PPED2SET_HPP_

