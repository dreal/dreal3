
/////////////////////////////////////////////////////////////////////////////
/// @file AffineSet.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_GEOMSET_AFFINESET_HPP_
#define _CAPD_GEOMSET_AFFINESET_HPP_

#include "capd/vectalg/iobject.hpp"
#include "capd/geomset/AffineSet.h"
#include <sstream>
//#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd {
namespace geomset {


/// sets x:=0, r:=0, B:=Id
template<typename MatrixType>
AffineSet<MatrixType>::AffineSet(int dim) :
  m_x(dim), m_r(dim), m_B(MatrixType::Identity(dim)) {
}

/// sets x:=mid(v),  B:=Id, r:=[-radius(v), radius(v)]
template<typename MatrixType>
AffineSet<MatrixType>::AffineSet(const VectorType& v) :
  m_x(v), m_r(v.dimension(), false), m_B(MatrixType::Identity(v.dimension())) {
  split(m_x, m_r);
}

/// sets x:=x,  B:=Id, r:=0
template<typename MatrixType>
AffineSet<MatrixType>::AffineSet(const VectorType& x, bool) :
  m_x(x), m_r(x.dimension()), m_B(MatrixType::Identity(x.dimension())) {
}

/// sets x:=x r:=r B:=Id
template<typename MatrixType>
AffineSet<MatrixType>::AffineSet(const VectorType& x, const VectorType& r) :
  m_x(x), m_r(r), m_B(MatrixType::Identity(x.dimension())) {
}
/// sets x:=x r:=r B:=B
template<typename MatrixType>
AffineSet<MatrixType>::AffineSet(const VectorType& x,
                                 const MatrixType& B, const VectorType& r)
  :  m_x(x), m_r(r), m_B(B) {
}

template<typename MatrixType>
typename AffineSet<MatrixType>::ScalarType AffineSet<MatrixType>::size() const {
  return capd::vectalg::size(m_x + m_B * m_r);
}

template<typename MatrixType>
std::string AffineSet<MatrixType>::toString(void) const {
  std::ostringstream descriptor;
  descriptor << " x=" << m_x << "\n B=" << m_B << "\n r=" << m_r << " ";
  return descriptor.str();
}

/**
 *  makes affine transformation of the set with matrix M and center c
 *
 *   M * (set - c)
 */
template<typename MatrixType>
typename AffineSet<MatrixType>::VectorType AffineSet<MatrixType>::affineTransformation(const MatrixType& A_M,
                                                                                       const VectorType& A_C) const {
  return A_M * (m_x - A_C) + (A_M * m_B) * m_r;
}

}
} // namespace capd::dynset

#endif // _CAPD_GEOMSET_AFFINESET_HPP_


