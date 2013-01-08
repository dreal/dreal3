
/////////////////////////////////////////////////////////////////////////////
/// @file MatrixDoubletonSet.hpp
///
/// @author kapela
/// Created on: Oct 24, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_GEOMSET_MATRIXDOUBLETONSET_HPP_
#define _CAPD_GEOMSET_MATRIXDOUBLETONSET_HPP_

#include "capd/geomset/MatrixDoubletonSet.h"
#include "capd/geomset/MatrixAffineSet.hpp"
#include "capd/vectalg/iobject.hpp"

#include <stdexcept>

namespace capd{
namespace geomset{

/// D:=Id, R0:=0, C:=Id, R:=0, B:=Id
template<typename MatrixType>
MatrixDoubletonSet<MatrixType>::MatrixDoubletonSet(int dim)
  : BaseSet(dim),
    m_R0(dim,dim,false),
    m_Cjac(MatrixType::Identity(dim)){
  m_R0.clear();
}

/// D:=mid(A), R0:=[-radius(A),radius(A)], C:=Id, R:=0, B:=Id
template<typename MatrixType>
MatrixDoubletonSet<MatrixType>::MatrixDoubletonSet(const MatrixType& A)
  : BaseSet(A.numberOfRows()),
    m_R0(A.numberOfRows(), A.numberOfColumns()),
    m_Cjac(MatrixType::Identity(A.numberOfRows())) {
  capd::vectalg::split(A.begin(), A.end(),  m_D.begin(), m_R0.begin());
}
/// D:=D, R0:=0, C:=Id, R:=0, B:=Id
template<typename MatrixType>
MatrixDoubletonSet<MatrixType>::MatrixDoubletonSet(const MatrixType& D, bool)
  : BaseSet(D, true),
    m_R0(D.numberOfRows(), D.numberOfColumns()),
    m_Cjac(MatrixType::Identity(D.numberOfRows())) {
    m_D.clear();
}


/// D:=D, R0:=R0, C:=Id, R:=0, B:=Id
template<typename MatrixType>
MatrixDoubletonSet<MatrixType>::MatrixDoubletonSet(const MatrixType& D, const MatrixType& R0)
  : BaseSet(D,false),  // do not split X into (X,R)
    m_R0(R0),
    m_Cjac(MatrixType::Identity(D.numberOfRows())){
}

template<typename MatrixType>
MatrixDoubletonSet<MatrixType>::MatrixDoubletonSet(const MatrixType& D, const MatrixType& C, const MatrixType& R0)
  : BaseSet(D, false),
    m_R0(R0),
    m_Cjac(C) {

  // we must assure that m_D\in m_D + m_Cjac*m_R0
  if(!subset(m_R,m_R0))
  {
    MatrixType centerR0=m_R0;
    split(centerR0,m_R0);
    // now the m_R0 is centered. We must add C*centerR0 to m_D
    m_D += m_Cjac*centerR0;
    // finally, we split m_D to the point and the rest is added to R
    split(m_D,m_R);
  }
}

template<typename MatrixType>
MatrixDoubletonSet<MatrixType>::MatrixDoubletonSet(
    const MatrixType& X,
    const MatrixType& C,
    const MatrixType& R0,
    const MatrixType& R
  ):BaseSet(X,R),
    m_R0(R0),
    m_Cjac(C) {
}

template<typename MatrixType>
MatrixDoubletonSet<MatrixType>::MatrixDoubletonSet(
    const MatrixType& X,
    const MatrixType& C,
    const MatrixType& R0,
    const MatrixType& B,
    const MatrixType& R

  ):BaseSet(X, B, R),
    m_R0(R0),
    m_Cjac(C) {
}

template<typename MatrixType>
void MatrixDoubletonSet<MatrixType>::setToIdentity(int dim){
   m_D = m_Bjac = m_Cjac = MatrixType::Identity(dim);
   m_R = m_R0 = MatrixType(dim, dim);
}

template<typename MatrixType>
std::string MatrixDoubletonSet<MatrixType>::toString() const {
  std::ostringstream descriptor;
  descriptor << BaseSet::toString()
             << "\n C="  << m_Cjac
             << "\n R0=" << m_R0 << " ";
  return descriptor.str();
}

template<typename MatrixType>
typename MatrixDoubletonSet<MatrixType>::MatrixType MatrixDoubletonSet<MatrixType>::affineMatrixTransformation(
      const MatrixType& A_M
  ) const {
  return A_M*(m_D) + (A_M*m_Cjac)*m_R0 + (A_M*m_Bjac)*m_R;
}


}} // namespace capd::geomset

#endif // _CAPD_GEOMSET_MATRIXDOUBLETONSET_HPP_
