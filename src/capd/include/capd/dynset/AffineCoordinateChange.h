/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file AffineCoordinateChange.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_DYNSET_AFFINECOORDINATECHANGE_H_
#define _CAPD_DYNSET_AFFINECOORDINATECHANGE_H_

namespace capd{
namespace dynset{

/**
 * Affine Coordinate system Change
 * y = y0 + B*(x-x0)
 */
template <typename MatrixT>
class AffineCoordinateChange{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  AffineCoordinateChange(const VectorType & x0, const MatrixType & B, const VectorType & y0): m_x0(x0), m_y0(y0), m_B(B){
  }
  /// returns x in the new coordinates
  VectorType operator()(const VectorType &x) const{
     return m_y0 + m_B * (x - m_x0);
  }
  /// returns defivative of coordinate change
  MatrixType operator[](const VectorType &x) const{
    return m_B;
  }
  AffineCoordinateChange inverse() const {
    return AffineCoordinateChange(m_y0, inverse(m_B), m_x0);
  }
private:
  VectorType m_x0, m_y0;
  MatrixType m_B;
};

}} // namespace capd::dynset

#endif //

/// @}


















