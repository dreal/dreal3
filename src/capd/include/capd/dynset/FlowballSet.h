/// @addtogroup dynset
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FlowballSet.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_FLOWBALLSET_H_ 
#define _CAPD_DYNSET_FLOWBALLSET_H_ 

#include <stdexcept>
#include "capd/dynset/C0Set.h"
#include "capd/vectalg/Norm.h"

namespace capd{
namespace dynset{

template<typename MatrixT>
class FlowballSet : public C0Set<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

  FlowballSet(): m_n(0){}
  FlowballSet(const NormType& aNorm, int dim);
  FlowballSet(const VectorType& x, const ScalarType& r, const NormType& aNorm);
  FlowballSet(const FlowballSet&);
  ~FlowballSet(){delete m_n;}
  virtual C0Set<MatrixType>* clone(void);
  virtual C0Set<MatrixType>* fresh(void);
  virtual C0Set<MatrixType>* cover(const VectorType& v);
  virtual ScalarType size(void);
  virtual VectorType center(void);
  virtual void move(capd::dynsys::DynSys<MatrixType>& dynsys);
  virtual void move(capd::dynsys::DynSys<MatrixType>& dynsys, FlowballSet& result) const;
  virtual std::string show(void) const;
  virtual operator VectorType() const;
  virtual VectorType affineTransformation(const MatrixType&, const VectorType&) const;

protected:
  VectorType m_x;
  ScalarType m_r;
  NormType *m_n;
};

// inline definitions

template<typename MatrixT>
inline FlowballSet<MatrixT>::operator typename FlowballSet<MatrixT>::VectorType(void) const
{
   return intervalBall(m_x,m_r);
}

template<typename MatrixType>
inline typename FlowballSet<MatrixType>::VectorType FlowballSet<MatrixType>::center(void)
{
  return m_x;
}

template<typename MatrixType>
inline C0Set<MatrixType>* FlowballSet<MatrixType>::clone(void)
{
  return new FlowballSet<MatrixType>(*this);
}

template<typename MatrixType>
inline FlowballSet<MatrixType>::FlowballSet(const NormType& n, int dim)
  : m_x(dim), m_n(n.clone())
{}

template<typename MatrixType>
inline FlowballSet<MatrixType>::FlowballSet(const FlowballSet& S)
  : m_x(S.m_x), m_r(S.m_r), m_n(S.m_n->clone())
{}

template<typename MatrixType>
inline C0Set<MatrixType>* FlowballSet<MatrixType>::fresh(void)
{
  return new FlowballSet<MatrixType>(*m_n,m_x.dimension());
}

template<typename MatrixType>
inline C0Set<MatrixType>* FlowballSet<MatrixType>::cover(const VectorType& v)
{
  return new FlowballSet<MatrixType>(midVector(v),(*m_n)(rightVector(v)-midVector(v)),*m_n);
}

}} // namespace capd::dynset

#endif // _CAPD_DYNSET_FLOWBALLSET_H_ 

/// @}
