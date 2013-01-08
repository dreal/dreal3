/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C0PpedSet.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0PPEDSET_H_
#define _CAPD_DYNSET_C0PPEDSET_H_

#include "capd/dynset/C0Set.h"
#include "capd/geomset/CenteredAffineSet.h"


namespace capd{
namespace dynset{

// C0Set<IVectorType,IMatrixType> is represented as : x + B*r
// move via inverse matrix - Lohner second method

template<typename MatrixT>
class C0PpedSet : public C0Set<MatrixT>, public capd::geomset::CenteredAffineSet<MatrixT>{

public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::geomset::CenteredAffineSet<MatrixT> BaseSet;
  typedef typename C0Set<MatrixT>::SetType SetType;
  typedef typename C0Set<MatrixT>::DynSysType DynSysType;

  explicit C0PpedSet(int dim) : BaseSet(dim) {}
  explicit C0PpedSet(const VectorType& x) : BaseSet(x) {}
  C0PpedSet(const VectorType& x, const VectorType& r) : BaseSet(x, r) {}
  C0PpedSet(const VectorType& x, const MatrixType& B, const VectorType& r) : BaseSet(x, B, r) {}
  /// @deprecated
  C0PpedSet(const VectorType& x, const VectorType& r, const MatrixType& B) : BaseSet(x, B, r) {}

  void move(capd::dynsys::DynSys<MatrixType>& dynsys);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys, C0PpedSet& result) const;
  virtual std::string show(void) const;
  operator VectorType() const;

protected:
  using BaseSet::m_x;
  using BaseSet::m_r;
  using BaseSet::m_B;
};

template<typename MatrixT>
inline C0PpedSet<MatrixT>::operator typename C0PpedSet<MatrixT>::VectorType() const {
  return  m_x+m_B*m_r;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0PPEDSET_H_

/// @}
