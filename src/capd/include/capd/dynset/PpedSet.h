/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file PpedSet.h
/// @deprecated
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSET_PPEDSET_H_ 
#define _CAPD_DYNSET_PPEDSET_H_ 

#include "capd/dynset/C0Set.h"

namespace capd{
namespace dynset{

///
/// Deprecated! Use C0PpedSet instead.
/// @deprecated
///
// C0Set<IVectorType,IMatrixType> is represented as : x + B*r
// move via inverse matrix - Lohner second method

template<typename MatrixT>
class PpedSet : public C0Set<MatrixT>{

public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  inline VectorType get_x () {return m_x;}
  inline VectorType get_r () {return m_r;}
  inline MatrixType get_B () {return m_B;}

  explicit PpedSet(int);
  explicit PpedSet(const VectorType& x);
  PpedSet(const VectorType& x, const VectorType& r);
  PpedSet(const VectorType& x, const VectorType& r, const MatrixType& B);
  ScalarType size(void);
  virtual C0Set<MatrixType>* clone(void);
  virtual C0Set<MatrixType>* fresh(void);
  virtual C0Set<MatrixType>* cover(const VectorType& v);
  virtual VectorType center(void);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys);
  void move(capd::dynsys::DynSys<MatrixType>& dynsys, PpedSet& result) const;
  virtual std::string show(void) const;
  operator VectorType() const;
  virtual VectorType affineTransformation(const MatrixType&, const VectorType&) const;

protected:
  VectorType m_x, m_r;
  MatrixType m_B;
};

// inline definitions

template<typename MatrixType>
inline typename PpedSet<MatrixType>::VectorType PpedSet<MatrixType>::center(void)
{
  return m_x;
}

template<typename MatrixT>
inline PpedSet<MatrixT>::operator typename PpedSet<MatrixT>::VectorType(void) const
{
  return m_x + m_B*m_r;
}

template<typename MatrixType>
inline C0Set<MatrixType>* PpedSet<MatrixType>::clone(void)
{
  return new PpedSet<MatrixType>(*this);
}

template<typename MatrixType>
inline C0Set<MatrixType>* PpedSet<MatrixType>::fresh(void)
{
  return new PpedSet<MatrixType>(m_x.dimension());
}

template<typename MatrixType>
inline C0Set<MatrixType>* PpedSet<MatrixType>::cover(const VectorType& v)
{
  return new PpedSet<MatrixType>(midVector(v),v-midVector(v));
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_PPEDSET_H_ 

/// @}
