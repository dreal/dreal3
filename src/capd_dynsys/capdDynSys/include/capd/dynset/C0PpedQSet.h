/////////////////////////////////////////////////////////////////////////////
/// @file C0PpedQSet.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0RECTSETQ_H_
#define _CAPD_DYNSET_C0RECTSETQ_H_

#include "capd/dynset/C0Set.h"
#include "capd/geomset/CenteredAffineSet.h"
#include "capd/dynset/ReorganizationPolicy.h"
#include "capd/dynset/C0Rect2Reorganization.h"
#include "capd/dynset/QRPolicy.h"

namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{


/**
 *  C0PpedQSet  set is represented as  x + B*r
 *
 *  where
 *    x - center point
 *    B - matrix ('change of coordinates')
 *    r - interval set (almost zero centered product of intervals)
 *
 */

template <typename MatrixT, typename QRPolicy = SelectedQRWithPivoting>
class C0PpedQSet : public C0Set<MatrixT>, public capd::geomset::CenteredAffineSet<MatrixT>{

public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::geomset::CenteredAffineSet<MatrixT> BaseSet;
  typedef typename C0Set<MatrixT>::SetType SetType;
  typedef typename C0Set<MatrixT>::DynSysType DynSysType;


  explicit C0PpedQSet(int dim) : BaseSet(dim), level(1.0e-15) {}
  explicit C0PpedQSet(const VectorType& x) : BaseSet(x), level(1.0e-15) {}
  C0PpedQSet(const VectorType& x, const VectorType& r) : BaseSet(x, r), level(1.0e-15) {}
  C0PpedQSet(const VectorType& x, const MatrixType& B, const VectorType& r) : BaseSet(x, B, r), level(1.0e-15) {}
  /// @deprecated
  C0PpedQSet(const VectorType& x, const VectorType& r, const MatrixType& B) : BaseSet(x, B, r), level(1.0e-15) {}
  virtual ~C0PpedQSet(){}
  /// computes image of the set after one step/iterate of the dynamical system
  void move(DynSysType & dynsys);
  /// computes image of the set after one step/iterate of the dynamical system and stores it in result
  void move(DynSysType & dynsys, C0PpedQSet& result) const;
  virtual std::string show(void) const;
  operator VectorType() const;
  /// if vectors are closer to be parallel more than given tolerance level one of them will be orthogonalized
  void setParallelTolerance(const ScalarType & level) { this->level = level; }
  ScalarType getParallelTolerance() const { return this->level; }
protected:
  using BaseSet::m_x;
  using BaseSet::m_r;
  using BaseSet::m_B;
  ScalarType level;
};
/// @}

template<typename MatrixT, typename QRPolicy>
inline C0PpedQSet<MatrixT,QRPolicy>::operator typename C0PpedQSet<MatrixT,QRPolicy>::VectorType() const {
  return  m_x+m_B*m_r;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0RECTSETQ_H_

