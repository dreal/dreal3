/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Pped2Set.h
/// @deprecated
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_PPED2SET_H_ 
#define _CAPD_DYNSET_PPED2SET_H_ 

#include "capd/dynset/C0Set.h"

namespace capd {
namespace dynset {

///
/// Deprecated! Use C0Pped2Set instead.
/// @deprecated
///
//  x + C*r0 + B*r
// Lohner - internal representation;
//   C*r0 - Lipschitz part
//   B*r  - 'errors' computed via parraleleograms
template <typename MatrixT>
class Pped2Set : public C0Set<MatrixT> {

public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType, MatrixType> NormType;

  inline VectorType get_x() {
    return m_x;
  }
  inline VectorType get_r() {
    return m_r;
  }
  inline VectorType get_r0() {
    return m_r0;
  }
  inline MatrixType get_B() {
    return m_B;
  }
  inline MatrixType get_C() {
    return m_C;
  }

  explicit Pped2Set(int);
  explicit Pped2Set(const VectorType& x);
  Pped2Set(const VectorType& x, const VectorType& r0);
  virtual C0Set<MatrixType>* clone(void);
  virtual C0Set<MatrixType>* fresh(void);
  virtual C0Set<MatrixType>* cover(const VectorType& v);
  ScalarType size(void);
  virtual VectorType center(void);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys, Pped2Set& result) const;
  operator VectorType() const;
  std::string show() const;
  virtual VectorType
      affineTransformation(const MatrixType&, const VectorType&) const;

protected:
  VectorType m_x, m_r, m_r0;
  MatrixType m_B, m_C;
};

// inline definitions

template <typename MatrixType>
inline typename Pped2Set<MatrixType>::VectorType Pped2Set<MatrixType>::center(
    void) {
  return m_x;
}

template <typename MatrixT>
inline Pped2Set<MatrixT>::operator typename Pped2Set<MatrixT>::VectorType(void) const {
  return m_x + m_C * m_r0 + m_B * m_r;
}

template <typename MatrixType>
inline C0Set<MatrixType>* Pped2Set<MatrixType>::clone(void) {
  return new Pped2Set(*this);
}

template <typename MatrixType>
inline C0Set<MatrixType>* Pped2Set<MatrixType>::fresh(void) {
  return new Pped2Set(m_x.dimension());
}

template <typename MatrixType>
inline C0Set<MatrixType>* Pped2Set<MatrixType>::cover(const VectorType& v) {
  return new Pped2Set<MatrixType> (midVector(v), v - midVector(v));
}

}
} // namespace capd::dynset

#endif // _CAPD_DYNSET_PPED2SET_H_ 
/// @}
