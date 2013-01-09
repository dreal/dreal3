/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Intv2Set.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_INTV2SET_H_ 
#define _CAPD_DYNSET_INTV2SET_H_ 

#include "capd/dynset/C0Set.h"


namespace capd{
namespace dynset{

/// Intv2Set: x + C*r0 + r
///
/// Lohner - internal representation;
///   C*r0 - Lipschitz part
///   r  -  'errors' computed via interval evaluation

template<typename MatrixT>
class Intv2Set : public C0Set<MatrixT> {
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  explicit Intv2Set(int dim);
  explicit Intv2Set(const VectorType& x);
  Intv2Set(const VectorType& x, const VectorType& r0);
  Intv2Set(const VectorType& x, const MatrixType& C, const VectorType& r0);
  virtual C0Set<MatrixType>* clone(void);
  virtual C0Set<MatrixType>* fresh(void);
  virtual C0Set<MatrixType>* cover(const VectorType &v);
  ScalarType size(void);
  virtual VectorType center(void);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys, Intv2Set& result) const;
  operator VectorType() const;
  std::string show(void) const;
  virtual VectorType affineTransformation(const MatrixType&, const VectorType&) const;

protected:
  VectorType m_x, m_r, m_r0;
  MatrixType m_C;
};

// inline definitions

template<typename MatrixType>
inline typename Intv2Set<MatrixType>::VectorType Intv2Set<MatrixType>::center(void)
{
  return m_x;
}

template<typename MatrixT>
inline Intv2Set<MatrixT>::operator typename Intv2Set<MatrixT>::VectorType(void) const
{
  return m_x + m_C*m_r0 + m_r;
}


template<typename MatrixType>
inline C0Set<MatrixType>* Intv2Set<MatrixType>::clone(void)
{
  return new Intv2Set<MatrixType>(*this);
}

template<typename MatrixType>
inline C0Set<MatrixType>* Intv2Set<MatrixType>::fresh(void)
{
  return new Intv2Set<MatrixType>(m_x.dimension());
}

template<typename MatrixType>
inline C0Set<MatrixType>* Intv2Set<MatrixType>::cover(const VectorType& v)
{
  return new Intv2Set<MatrixType>(midVector(v),v-midVector(v));
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_INTV2SET_H_ 

/// @}
