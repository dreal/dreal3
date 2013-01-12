
/////////////////////////////////////////////////////////////////////////////
/// @file Rect2Set.h
///
///  Deprecated! Use C0Rect2RSet.h instead!
///  @deprecated
///
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2009 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_RECT2SET_H_
#define _CAPD_DYNSET_RECT2SET_H_

#include "capd/dynset/C0Rect2RSet.h"
namespace capd{
namespace dynset{


/////////////////////////////////////////////////////////////////////
///
///  Deprecated! Use class C0Rect2RSet instead!
///  @deprecated
///
///////////////////////////////////////////////////////////////////////

template <typename MatrixT,typename QRPolicy=FullQRWithPivoting>
class Rect2Set : public C0Rect2RSet<MatrixT,QRPolicy> {

public :
  typedef C0Rect2RSet<MatrixT,QRPolicy>  BaseSet;
  typedef typename BaseSet::MatrixType MatrixType;
  typedef typename BaseSet::VectorType VectorType;
  typedef typename BaseSet::ScalarType ScalarType;
  typedef typename BaseSet::NormType NormType;
  typedef typename BaseSet::ReorganizationPolicy ReorganizationPolicy;
  typedef typename BaseSet::SetType SetType;


  Rect2Set(BaseSet & set) : BaseSet(set){
  }
  explicit Rect2Set(int dim, double factor=1) : BaseSet(dim, factor) {}
  explicit Rect2Set(const VectorType& x, double factor=1) : BaseSet(x, factor) {}
  Rect2Set(const VectorType& x, const VectorType& r0, double factor=1) : BaseSet(x, r0, factor) {}
  Rect2Set(const VectorType& x, const MatrixType& C, const VectorType& r0, double factor=1
  ) : BaseSet(x, C, r0, factor) {}
  Rect2Set(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const VectorType& r, double factor=1
  ) : BaseSet(x, C, r0, r, factor) {}
  Rect2Set(const VectorType& x, const MatrixType& C,
      const VectorType& r0, const MatrixType& B,
      const VectorType& r, double factor=1
  ) : BaseSet(x, C, r0, B, r, factor) {}

  std::string name() const { return "Rect2Set"; }

  SetType *clone(void) const {
    return new Rect2Set(*this);
  }
  SetType *fresh(void) const {
    return new Rect2Set(this->m_x.dimension());
  }
  SetType *cover(const VectorType &v) const {
    return new Rect2Set(v);
  }
  ScalarType size(void) const {
    return capd::vectalg::size( this->m_x + this->m_C*this->m_r0 + this->m_B*this->m_r );
  }
  VectorType center(void) const {
    return this->m_x;
  }

};


}} // namespace capd::dynset

#endif // _CAPD_DYNSET_RECT2SET_H_
