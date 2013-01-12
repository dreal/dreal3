/////////////////////////////////////////////////////////////////////////////
/// @file CoordinateSystem.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_COORDINATESYSTEM_H_
#define _CAPD_DYNSET_COORDINATESYSTEM_H_
#include "capd/dynset/AffineCoordinateChange.h"
namespace capd {
namespace dynset {
/// @addtogroup dynset
/// @{

/**
 * Defines coordinate system.
 *
 * Coordinate System is given by
 * center and matrix of base vectors (as its columns).
 */
template<typename MatrixT>
class CoordinateSystem {
public:
  typedef MatrixT MatrixType;
    typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  CoordinateSystem(const VectorType & x0, const MatrixType & B):
    m_x0(x0), m_B(B){
    VectorType zero(x0.dimension());
    x0.clear();
    changeFromSystem(x0, B, zero);
    changeToSystem = changeFromSystem.inverse();
  }
  VectorType convertTo(const VectorType & v) {
    return changeToSystem(v);
  }
  VectorType convertFrom(const VectorType & v) {
    changeFromSystem(v);
  }
private:
  VectorType m_x0;
  MatrixType m_B;
  AffineCoordinateChange<MatrixType> changeToSystem,
                                     changeFromSystem;
};

/// @}
}} // namespace capd::dynset

#endif //



