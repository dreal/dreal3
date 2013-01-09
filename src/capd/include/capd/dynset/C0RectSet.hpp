/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C0RectSet.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0RECTSET_HPP_
#define _CAPD_DYNSET_C0RECTSET_HPP_

#include "capd/vectalg/iobject.hpp"
#include "capd/dynset/C0RectSet.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"


namespace capd{
namespace dynset{

template<typename MatrixType, typename QRPolicy>
void C0RectSet<MatrixType,QRPolicy>::move(DynSysType & dynsys) {
  move(dynsys,*this);
}

template<typename MatrixType, typename QRPolicy>
void C0RectSet<MatrixType,QRPolicy>::move(DynSysType & dynsys, C0RectSet& result) const {

  VectorType y(m_x.dimension()), rem(m_x.dimension());
  MatrixType A(m_x.dimension(), m_x.dimension());

  VectorType xx = m_x + m_B * m_r;
  dynsys.encloseMap(m_x, xx, y, A, rem);

  result.m_x = y + rem;
  MatrixType D = A*m_B;
// xx is unnecessary, we can use it again
  split(result.m_x,xx);
  mid(D,result.m_B);
  QRPolicy::orthonormalize(result.m_B,m_r);
  MatrixType Qtr = Transpose(result.m_B);
  result.m_r = (Qtr*D)*m_r + Qtr*xx;
}

template<typename MatrixType, typename QRPolicy>
std::string C0RectSet<MatrixType,QRPolicy>::show(void) const
{
  //std::ostringstream descriptor;
  //descriptor << "C0RectSet:\n" << toString();
  //return descriptor.str();
  return "C0RectSet:\n" + BaseSet::toString();
}


}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0RECTSET_HPP_

/// @}


















