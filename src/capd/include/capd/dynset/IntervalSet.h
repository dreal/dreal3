/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file IntvSet.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_INTVSET_H_ 
#define _CAPD_DYNSET_INTVSET_H_ 

#include "capd/dynset/C0Set.h"


namespace capd{
namespace dynset{

/// moved  by  Jac*x + remainder
template<typename MatrixT>
class IntervalSet : public C0Set<MatrixT>
{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  IntervalSet(void);
  explicit IntervalSet(int);
  explicit IntervalSet(const VectorType& x);
  IntervalSet(const VectorType& x,const VectorType& r);
  virtual C0Set<MatrixType>* clone(void);
  virtual C0Set<MatrixType>* fresh(void);
  virtual C0Set<MatrixType>* cover(const VectorType& v);
  virtual ScalarType size(void);
  virtual VectorType center(void);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys, IntervalSet& result) const;
  virtual std::string show(void) const;
  virtual operator VectorType() const;
  VectorType get_r();
  virtual VectorType affineTransformation(const MatrixType&, const VectorType&) const;

protected:
  VectorType m_x, m_r;
};

// inline definitions


template<typename MatrixType>
inline typename IntervalSet<MatrixType>::VectorType IntervalSet<MatrixType>::center(void)
{
  return m_x;
}

template<typename MatrixT>
inline IntervalSet<MatrixT>::operator typename IntervalSet<MatrixT>::VectorType(void) const
{
  return m_x + m_r;
}

template<typename MatrixType>
inline C0Set<MatrixType>* IntervalSet<MatrixType>::clone(void)
{
  return new IntervalSet<MatrixType>(*this);
}

template<typename MatrixType>
inline C0Set<MatrixType>* IntervalSet<MatrixType>::fresh(void)
{
  return new IntervalSet<MatrixType>(m_x.dimension());
}

template<typename MatrixType>
inline C0Set<MatrixType>* IntervalSet<MatrixType>::cover(const VectorType& v)
{
  return new IntervalSet<MatrixType>(midVector(v),v-midVector(v));
}

template<typename MatrixType>
inline typename IntervalSet<MatrixType>::VectorType IntervalSet<MatrixType>::get_r()
{
  return m_r;
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_INTVSET_H_ 

/// @}
