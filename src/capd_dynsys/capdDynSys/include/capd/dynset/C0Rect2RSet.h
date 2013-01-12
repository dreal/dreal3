/////////////////////////////////////////////////////////////////////////////
///
/// @file C0Rect2RSet.h
///
/// @author kapela
/// Created on: Oct 25, 2009
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_C0RECT2RSET_H_
#define _CAPD_DYNSET_C0RECT2RSET_H_

#include "capd/dynset/ReorganizedSet.h"
#include "capd/dynset/C0Rect2Reorganization.h"
#include "capd/dynset/C0Rect2Set.h"
namespace capd{
namespace dynset{
// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////
///
///  This is C0Rect2Set with built-in default reorganization
///
///////////////////////////////////////////////////////////////////////
template <typename MatrixT, typename QRPolicy = FullQRWithPivoting>
class C0Rect2RSet : public ReorganizedSet<C0Rect2Set<MatrixT,QRPolicy>, C0Rect2Reorganization<C0Rect2Set<MatrixT,QRPolicy> > > {

public :
  typedef ReorganizedSet<C0Rect2Set<MatrixT,QRPolicy>, C0Rect2Reorganization<C0Rect2Set<MatrixT,QRPolicy> > > BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename BaseSet::VectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename C0Rect2RSet<MatrixT,QRPolicy>::NormType NormType;
  typedef typename BaseSet::ReorganizationPolicy ReorganizationPolicy;

  C0Rect2RSet(BaseSet & set) : BaseSet(set){
  }
  explicit C0Rect2RSet(int dim, double factor=1) : BaseSet(dim) {
    setFactor(factor);
  }
  explicit C0Rect2RSet(const VectorType& x, double factor=1) : BaseSet(x) {
    setFactor(factor);
  }
  C0Rect2RSet(const VectorType& x, const VectorType& r0, double factor=1) : BaseSet(x, r0) {
    setFactor(factor);
  }
  C0Rect2RSet(const VectorType& x, const MatrixType& C, const VectorType& r0, double factor=1
  ) : BaseSet(x, C, r0) {
    setFactor(factor);
  }
  C0Rect2RSet(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const VectorType& r, double factor=1
  ) : BaseSet(x, C, r0, r) {
    setFactor(factor);
  }
  C0Rect2RSet(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const MatrixType& B,
      const VectorType& r, double factor=1
  ) : BaseSet(x, C, r0, B, r) {
    setFactor(factor);
  }

  void setFactor(double factor){
    BaseSet::setFactor(factor);
  }
  std::string name() const { return "C0Rect2RSet"; }
};

/// @}
}} // namespace capd::dynset

#endif // _CAPD_DYNSET_C0RECT2RSET_H_

