

/////////////////////////////////////////////////////////////////////////////
/// @file CenteredDoubletonSet.hpp
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_GEOMSET_CENTEREDDOUBLETONSET_HPP_
#define _CAPD_GEOMSET_CENTEREDDOUBLETONSET_HPP_

#include "capd/geomset/DoubletonSet.hpp"
#include "capd/geomset/CenteredDoubletonSet.h"

namespace capd{
namespace geomset{

template<typename MatrixType>
CenteredDoubletonSet<MatrixType>::CenteredDoubletonSet(const VectorType& v)
  : BaseSet(v){
 // already splitted in DoubletonSet  split(m_r0, m_x, m_r0);
}

template<typename MatrixType>
CenteredDoubletonSet<MatrixType>::CenteredDoubletonSet(const VectorType& x, const VectorType& r0)
  : BaseSet(x, r0){
  // we must assure that m_x\in m_x + m_r0
  // m_r is zero, so we verify if m_r is a subset of m_r0
  if(!subset(m_r, m_r0)) {
    m_x += m_r0;
    split(m_x,m_r0);
  }
}

template<typename MatrixType>
CenteredDoubletonSet<MatrixType>::CenteredDoubletonSet(const VectorType& x, const MatrixType& C, const VectorType& r0)
  : BaseSet(x, C, r0) {

  // we must assure that m_x\in m_x + m_C*m_r0
  if(!subset(m_r,m_r0))
  {
    VectorType centerR0=m_r0;
    split(centerR0,m_r0);
    // now the m_r0 is centered. We must add C*centerR0 to m_x
    m_x += m_C*centerR0;
    // finally, we split m_x to the point and the rest is added to r
    split(m_x,m_r);
  }
}

template<typename MatrixType>
CenteredDoubletonSet<MatrixType>::CenteredDoubletonSet(
    const VectorType& x,
    const MatrixType& C,
    const VectorType& r0,
    const VectorType& r
  ): BaseSet(x, C, r0, r) {
  VectorType zero(x.dimension());
  if( !( subset(zero,m_r0) && subset(zero,m_r) ) )
  {
    VectorType centerR0=m_r0;
    split(centerR0,m_r0);
    // now the m_r0 is centered. We must add C*centerR0 to m_x
    m_x += m_C*centerR0;
    // finally, we split m_x to the point and the rest is added to r
    m_x += m_r;
    split(m_x,m_r);
  }
}

template<typename MatrixType>
CenteredDoubletonSet<MatrixType>::CenteredDoubletonSet(
    const VectorType& x,
    const MatrixType& C,
    const VectorType& r0,
    const MatrixType& B,
    const VectorType& r

  ):BaseSet(x, C, r0, B, r) {
  VectorType zero(x.dimension());
  if( !( subset(zero,m_r0) && subset(zero,m_r) ) ) {   // If fact we could center this set but most probably it is programmers mistake
    throw std::runtime_error ("Wrong vectors in a constructor of CenteredDoubletonSet.");  // so we prefer to throw an exception
  }
}
}} //capd::geomset

#endif // _CAPD_GEOMSET_CENTEREDDOUBLETONSET_HPP_


