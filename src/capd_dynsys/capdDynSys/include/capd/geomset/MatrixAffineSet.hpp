/////////////////////////////////////////////////////////////////////////////
/// @file MatrixAffineSet.hpp
///
/// @author kapela
/// Created on: Oct 24, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_MATRIXAFFINESET_HPP_
#define _CAPD_MATRIXAFFINESET_HPP_


//#include "capd/vectalg/iobject.hpp"
#include "capd/geomset/MatrixAffineSet.h"
//#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd {
namespace geomset {


/// A:=ID, R:=0, B:=Id
template<typename MatrixType>
MatrixAffineSet<MatrixType>::MatrixAffineSet(int dim) :
  m_D(MatrixType::Identity(dim)), m_R(dim,dim), m_Bjac(MatrixType::Identity(dim)) {
}

/// A:=mid(v),  B:=Id, R:=[-radius(v), radius(v)]
template<typename MatrixType>
MatrixAffineSet<MatrixType>::MatrixAffineSet(const MatrixType& A) :
  m_D(A), m_R(A.numberOfRows(),A.numberOfColumns(), false), m_Bjac(MatrixType::Identity(A.numberOfRows())) {
  split(m_D, m_R);
}

/// A:=A,  B:=Id, R:=0
template<typename MatrixType>
MatrixAffineSet<MatrixType>::MatrixAffineSet(const MatrixType& A, bool) :
  m_D(A), m_R(A.numberOfRows(),A.numberOfColumns()), m_Bjac(MatrixType::Identity(A.numberOfRows())) {
}

/// A:=A R:=R B:=Id
template<typename MatrixType>
MatrixAffineSet<MatrixType>::MatrixAffineSet(const MatrixType& A, const MatrixType& R) :
  m_D(A), m_R(R), m_Bjac(MatrixType::Identity(A.numberOfRows())) {
}
/// A:=A R:=R B:=B
template<typename MatrixType>
MatrixAffineSet<MatrixType>::MatrixAffineSet(const MatrixType& A,
                                 const MatrixType& B, const MatrixType& R)
  :  m_D(A), m_R(R), m_Bjac(B) {
}


template<typename MatrixType>
void MatrixAffineSet<MatrixType>::setToIdentity(int dim){
   m_D = m_Bjac = MatrixType::Identity(dim);
   m_R = MatrixType(dim, dim);
}

template<typename MatrixType>
std::string MatrixAffineSet<MatrixType>::toString(void) const {
  std::ostringstream descriptor;
  descriptor << " D=" << m_D << "\n B=" << m_Bjac << "\n R=" << m_R << " ";
  return descriptor.str();
}


/**
 * makes affine transformation of set, transformation is given by matrix M
 *   result = M * set
 */
template<typename MatrixType>
typename MatrixAffineSet<MatrixType>::MatrixType MatrixAffineSet<MatrixType>::affineMatrixTransformation(
    const MatrixType& A_M) const {
  return A_M * m_D + (A_M * m_Bjac) * m_R;
}

}
} // namespace capd::dynset

#endif // _CAPD_MATRIXAFFINESET_HPP_


