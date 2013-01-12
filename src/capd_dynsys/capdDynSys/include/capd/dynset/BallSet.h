
/////////////////////////////////////////////////////////////////////////////
/// @file BallSet.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_BALLSET_H_ 
#define _CAPD_DYNSET_BALLSET_H_ 

#include "capd/dynset/C0Set.h"
#include "capd/vectalg/Norm.h"

namespace capd{
namespace dynset{
/// @addtogroup dynset
/// @{

/**
   the set is represented as: x + Ball(r).

   move: x - center of result; r = Lip(JacPhi) + errors from Phi(x)
      for cascades
      for flows : r = exp(Lip(vectfield)*h) + errors ..
 */
template<typename MatrixT>
class BallSet : public C0Set<MatrixT>{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef capd::vectalg::Norm<VectorType,MatrixType> NormType;

protected:
  VectorType x;
  ScalarType r;
  NormType *n;

public:
  BallSet() : n(0) {}
  BallSet(const BallSet&);
  BallSet(const VectorType &the_x,const ScalarType &the_r, NormType &the_n);
  ~BallSet();
  const BallSet& operator=(const BallSet&);

  virtual C0Set<MatrixType> *clone(void);
  virtual C0Set<MatrixType> *fresh(void);
  virtual C0Set<MatrixType> *cover(const VectorType &v);
  virtual ScalarType size(void);
  virtual VectorType center(void);
  virtual void move(capd::dynsys::DynSys<MatrixType> &dynsys);
  virtual void move(capd::dynsys::DynSys<MatrixType> &dynsys, BallSet &result) const;
  virtual std::string show(void) const;
  virtual operator VectorType() const;
  virtual VectorType affineTransformation(const MatrixType&, const VectorType&) const;
};

/// @}

/******************** inline definitions ***********************/

template<typename MatrixType>
inline BallSet<MatrixType>::BallSet(const BallSet& a_set)
  : x(a_set.x), r(a_set.r), n(a_set.n->clone())
{}

template<typename MatrixType>
inline const BallSet<MatrixType>& BallSet<MatrixType>::operator=(const BallSet& a_set)
{
  x = a_set.x;
  r = a_set.r;
  delete n;
  n = a_set.n->clone();
  return *this;
}

template<typename MatrixType>
inline BallSet<MatrixType>::~BallSet()
{
  delete n;
}

template<typename MatrixT>
inline BallSet<MatrixT>::operator typename BallSet<MatrixT>::VectorType(void) const
{
  return intervalBall(x,r);
}

template<typename MatrixType>
inline typename BallSet<MatrixType>::VectorType BallSet<MatrixType>::center(void)
{
  return x;
}

template<typename MatrixType>
inline BallSet<MatrixType>::BallSet(const VectorType& a_x, const ScalarType& a_r, NormType& a_n)
  : x(a_x), r(a_r), n(a_n.clone())
{}

template<typename MatrixType>
inline C0Set<MatrixType>* BallSet<MatrixType>::clone(void)
{
  return new BallSet<MatrixType>(*this);
}

template<typename MatrixType>
inline C0Set<MatrixType>* BallSet<MatrixType>::fresh(void)
{
  return new BallSet<MatrixType>;
}

template<typename MatrixType>
inline C0Set<MatrixType>* BallSet<MatrixType>::cover(const VectorType &v)
{
  return new BallSet<MatrixType>(midVector(v),(*n)(rightVector(v)-midVector(v)),*n);
}



}} // namespace capd::dynset

#endif // _CAPD_DYNSET_BALLSET_H_ 


