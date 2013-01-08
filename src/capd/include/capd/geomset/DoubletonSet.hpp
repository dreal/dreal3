
/////////////////////////////////////////////////////////////////////////////
/// @file DoubletonSet.hpp
///
/// @author kapela
/// Created on: Oct 21, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#ifndef _CAPD_GEOMSET_DOUBLETONSET_HPP_
#define _CAPD_GEOMSET_DOUBLETONSET_HPP_
#include "capd/geomset/DoubletonSet.h"
#include "capd/geomset/AffineSet.hpp"
#include <sstream>

#include <stdexcept>

namespace capd{
namespace geomset{

/// x:=0, r0:=0, C:=Id, r:=0, r:=Id
template<typename MatrixType>
DoubletonSet<MatrixType>::DoubletonSet(int dim)
  : BaseSet(dim),
    m_r0(dim),
    m_C(MatrixType::Identity(dim)){
  m_r0.clear();
}

/// x:=mid(v), r0:=[-radius(v),radius(v)], C:=Id, r:=0, r:=Id
template<typename MatrixType>
DoubletonSet<MatrixType>::DoubletonSet(const VectorType& v)
  : BaseSet(v.dimension()),
    m_r0(v),
    m_C(MatrixType::Identity(v.dimension())) {
  split(m_r0, m_x, m_r0);
}
/// x:=0, r0:=r0, C:=Id, r:=0, r:=Id
template<typename MatrixType>
DoubletonSet<MatrixType>::DoubletonSet(const VectorType& r0, bool)
  : BaseSet(r0.dimension()),
    m_r0(r0),
    m_C(MatrixType::Identity(r0.dimension())) {
}


/// x:=x, r0:=r0, C:=Id, r:=0, r:=Id
template<typename MatrixType>
DoubletonSet<MatrixType>::DoubletonSet(const VectorType& x, const VectorType& r0)
  : BaseSet(x,false),  // do not split x into (x,r)
    m_r0(r0),
    m_C(MatrixType::Identity(x.dimension())){
}

template<typename MatrixType>
DoubletonSet<MatrixType>::DoubletonSet(const VectorType& x, const MatrixType& C, const VectorType& r0)
  : BaseSet(x, false),
    m_r0(r0),
    m_C(C) {
}

template<typename MatrixType>
DoubletonSet<MatrixType>::DoubletonSet(
    const VectorType& x,
    const MatrixType& C,
    const VectorType& r0,
    const VectorType& r
  ):BaseSet(x,r),
    m_r0(r0),
    m_C(C) {

}

template<typename MatrixType>
DoubletonSet<MatrixType>::DoubletonSet(
    const VectorType& x,
    const MatrixType& C,
    const VectorType& r0,
    const MatrixType& B,
    const VectorType& r
  ):BaseSet(x, B, r),
    m_r0(r0),
    m_C(C) {
}

template<typename MatrixType>
DoubletonSet<MatrixType> & DoubletonSet<MatrixType>::operator=(const VectorType & x){
   int dim = x.dimension();
   m_x = x;
   m_r0 = VectorType(dim);
   split(m_x,m_r0);
   m_B = m_C = MatrixType::Identity(dim);
   m_r = VectorType(dim);
   //m_r.clear();
   return *this;
}

template<typename MatrixType>
typename DoubletonSet<MatrixType>::ScalarType DoubletonSet<MatrixType>::size() const {
  return capd::vectalg::size( m_x + m_C*m_r0 + m_B*m_r );
}


template<typename MatrixType>
std::string DoubletonSet<MatrixType>::toString() const {
  std::ostringstream descriptor;
  descriptor << BaseSet::toString()
             << "\n C="  << m_C
             << "\n r0=" << m_r0 << " ";
  return descriptor.str();
}

template<typename MatrixType>
typename DoubletonSet<MatrixType>::VectorType DoubletonSet<MatrixType>::affineTransformation(
      const MatrixType& A_M, const VectorType& A_C
  ) const {
  return A_M*(m_x-A_C) + (A_M*m_C)*m_r0 + (A_M*m_B)*m_r;
}

}} // namespace capd::geomset

#endif // _CAPD_GEOMSET_DOUBLETONSET_HPP_

