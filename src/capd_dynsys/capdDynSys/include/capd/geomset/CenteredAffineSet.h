
/////////////////////////////////////////////////////////////////////////////
/// @file CenteredAffineSet.h
///
/// @author kapela
/// Created on: Oct 21, 2009
// ///////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_GEOMSET_CENTEREDAFFINESET_H_
#define _CAPD_GEOMSET_CENTEREDAFFINESET_H_

#include "capd/geomset/AffineSet.hpp"
namespace capd {
namespace geomset {
/// @addtogroup geomset
/// @{

/**
 * Affine set representation of the form x + B * r which assures that r contains zero.
 *
 * CenteredAffineSet represents set of the form
 *
 *   x + B * r
 *
 * where
 * - the vector x is a center,
 * - the matrix B is a coordinate system
 * - the vector r is a product of intervals and represents the set in a given coordinate system.
 * Constructors assures that r contains zero.
 */
template<typename MatrixT>
class CenteredAffineSet : public capd::geomset::AffineSet<MatrixT> {

public:
  typedef capd::geomset::AffineSet<MatrixT> BaseSet;
  typedef MatrixT MatrixType;
  typedef  typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ColumnVectorType ColumnVectorType;
  typedef typename MatrixType::ScalarType ScalarType;

  /// x:=0 r:=0 B:=Id
  explicit CenteredAffineSet(int dim) : BaseSet(dim) {
  }
  /// x:=mid(v)  r:=[-radius(v),radius(v)]  B:=Id
  CenteredAffineSet(const VectorType& v) : BaseSet(v){
     // splitting already done in AffineSet
  }
  /// We do not split x
  /// x:= x, r:=0, B:=Id
  CenteredAffineSet(const VectorType& x, bool) : BaseSet(x, true){
  }
  CenteredAffineSet(const VectorType& x, const VectorType& r) : BaseSet(x,r){
    if (!subset(VectorType(x.dimension()), m_r)) { // if m_r do not contain zero
      m_x += m_r;                                  //   we center the set
      split(m_x, m_r);
    }
  }

  CenteredAffineSet(const VectorType& x,
                    const MatrixType& B, const VectorType& r)
    :  BaseSet(x,B,r) {
    if (!subset(VectorType(x.dimension()), m_r)) {   // if m_r do not contain zero
      VectorType centerR = m_r;                      //   we center the set
      split(centerR, m_r);
      // m_x will be not a single point, but we must assure m_r contains zero
      m_x += m_B * centerR;
    }
  }

  virtual std::string name() const { return "CenteredAffineSet"; }

  using BaseSet::m_x;
  using BaseSet::m_B;
  using BaseSet::m_r;

};

/// @}
}} //capd::geomset

#endif // _CAPD_GEOMSET_CENTEREDAFFINESET_H_

