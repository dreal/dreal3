/////////////////////////////////////////////////////////////////////////////
/// @file C0Rect2Set.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0RECT2SET_H_
#define _CAPD_DYNSET_C0RECT2SET_H_

#include "capd/dynset/C0Set.h"
#include "capd/geomset/CenteredDoubletonSet.hpp"
#include "capd/dynset/ReorganizationPolicy.h"
#include "capd/dynset/C1Rect2Reorganization.h"
#include "capd/dynset/QRPolicy.h"


namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////
///
///  The set is represented as doubleton: x + C*r0 + B*r;
///  and is moved by Lohner last method.
///
///  internal representation :
///        C*r0 - basic 'Lipschitz part'
///        B*r  - QR-decomposition of the remaining errors
///
///////////////////////////////////////////////////////////////////////
template<typename MatrixT, typename QRPolicy = FullQRWithPivoting >
class C0Rect2Set : public C0Set<MatrixT>, public capd::geomset::CenteredDoubletonSet<MatrixT>{

public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;
  typedef capd::geomset::CenteredDoubletonSet<MatrixT> BaseSet;
  typedef bool C0Rect;
  typedef typename C0Set<MatrixT>::SetType SetType;
  typedef typename C0Set<MatrixT>::DynSysType DynSysType;

  explicit C0Rect2Set(int dim) : BaseSet(dim) {}
  explicit C0Rect2Set(const VectorType& x) : BaseSet(x) {}
  C0Rect2Set(const VectorType& x, const VectorType& r0) : BaseSet(x, r0) {}
  C0Rect2Set(const VectorType& x, const MatrixType& C, const VectorType& r0
  ) : BaseSet(x, C, r0) {}
  C0Rect2Set(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const VectorType& r
  ) : BaseSet(x, C, r0, r) {}
  C0Rect2Set(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const MatrixType& B,
      const VectorType& r
  ) : BaseSet(x, C, r0, B, r) {}
  /// computes image of the set after one step/iterate of the dynamical system
  void move(DynSysType & dynsys);
  /// computes image of the set after one step/iterate of the dynamical system and stores it in result
  void move(DynSysType & dynsys, C0Rect2Set& result) const;
  operator VectorType() const{
    return BaseSet::operator VectorType();
  }

  std::string show() const;
  std::string name() const { return "C0Rect2Set"; }
protected:
  using BaseSet::m_x;
  using BaseSet::m_r;
  using BaseSet::m_r0;
  using BaseSet::m_B;
  using BaseSet::m_C;
};
/// @}

template <typename MatrixType, typename QRPolicy>
class ReorganizationPolicy<C0Rect2Set<MatrixType,QRPolicy> > {
  public:
  typedef C0Rect2Reorganization<C0Rect2Set<MatrixType,QRPolicy> > DefaultReorganization;
};

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0RECT2SET_H_
