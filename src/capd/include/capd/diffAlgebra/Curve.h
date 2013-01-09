/// @addtogroup diffAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Curve.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#ifndef _CAPD_DIFFALGEBRA_CURVE_H_
#define _CAPD_DIFFALGEBRA_CURVE_H_

#include <stdexcept>
#include "capd/capd/TypeTraits.h"

namespace capd{
namespace diffAlgebra{

template<class MatrixT>
class Curve
{
public:
  typedef MatrixT MatrixType;
  typedef typename MatrixType::RowVectorType VectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef typename TypeTraits<ScalarType>::Real Real;
  
  
  Curve(Real left, Real right, int dimension, int order);
  Curve(const Curve& c);
  ~Curve();
  
  Curve& operator=(const Curve& c);
  
  void setOrder(int order);
  int getOrder() const;
  int getAllocatedOrder() const;
  int dimension() const;
  void setDomain(Real left, Real right);
  Real getLeftDomain() const;
  Real getRightDomain() const;

  VectorType operator()(const ScalarType& h) const;
  MatrixType operator[](const ScalarType& h) const;

  const VectorType* getCoefficientsAtCenter() const;
  const VectorType* getCoefficients() const;
  const VectorType* getRemainderCoefficients() const;
  
  const MatrixType* getMatrixCoefficients() const;
  const MatrixType* getMatrixRemainderCoefficients() const;
  
   VectorType* getCoefficientsAtCenter();
   VectorType* getCoefficients();
   VectorType* getRemainderCoefficients();
  
   MatrixType* getMatrixCoefficients();
   MatrixType* getMatrixRemainderCoefficients();
   
   void clearCoefficients();
   
   Curve derivative() const;

protected:

  void allocate();
  void deallocate();
  void copyData(const Curve& c);
  
  VectorType *m_coefficientsAtCenter;
  VectorType *m_coefficients;
  VectorType *m_remainderCoefficients;

  MatrixType *m_matrixCoefficients;
  MatrixType *m_matrixRemainderCoefficients;
  
  Real m_left, m_right; ///< domain
  int m_order;
  int m_allocatedOrder;
  int m_dimension;
};

// ----------------- inline definitions ------------------

template<class MatrixT>
inline
int Curve<MatrixT>::getOrder() const
{
  return this->m_order;
}
  
template<class MatrixT>
inline
int Curve<MatrixT>::getAllocatedOrder() const
{
  return this->m_allocatedOrder;
}

template<class MatrixT>
inline
int Curve<MatrixT>::dimension() const
{
  return this->m_dimension;
}

template<class MatrixT>
inline
void Curve<MatrixT>::setDomain(Real left, Real right)
{
  this->m_left = left;
  this->m_right = right;
}

template<class MatrixT>
inline
typename Curve<MatrixT>::Real Curve<MatrixT>::getLeftDomain() const
{
  return this->m_left;
}

template<class MatrixT>
inline
typename Curve<MatrixT>::Real Curve<MatrixT>::getRightDomain() const
{
  return this->m_right;
}

template<class MatrixT>
inline 
const typename Curve<MatrixT>::VectorType* Curve<MatrixT>::getCoefficientsAtCenter() const
{
  return this->m_coefficientsAtCenter;
}

template<class MatrixT>
inline
const typename Curve<MatrixT>::VectorType* Curve<MatrixT>::getCoefficients() const
{
  return this->m_coefficients;
}

template<class MatrixT>
const typename Curve<MatrixT>::VectorType* Curve<MatrixT>::getRemainderCoefficients() const
{
  return this->m_remainderCoefficients;
}
  
template<class MatrixT>
const MatrixT* Curve<MatrixT>::getMatrixCoefficients() const
{
  return this->m_matrixCoefficients;
}

template<class MatrixT>
const MatrixT* Curve<MatrixT>::getMatrixRemainderCoefficients() const
{
  return this->m_matrixRemainderCoefficients;
}

template<class MatrixT>
inline 
typename Curve<MatrixT>::VectorType* Curve<MatrixT>::getCoefficientsAtCenter() 
{
  return this->m_coefficientsAtCenter;
}

template<class MatrixT>
inline
typename Curve<MatrixT>::VectorType* Curve<MatrixT>::getCoefficients() 
{
  return this->m_coefficients;
}

template<class MatrixT>
typename Curve<MatrixT>::VectorType* Curve<MatrixT>::getRemainderCoefficients() 
{
  return this->m_remainderCoefficients;
}
  
template<class MatrixT>
MatrixT* Curve<MatrixT>::getMatrixCoefficients() 
{
  return this->m_matrixCoefficients;
}

template<class MatrixT>
MatrixT* Curve<MatrixT>::getMatrixRemainderCoefficients() 
{
  return this->m_matrixRemainderCoefficients;
}

}} // namespace capd::diffAlgebra

#endif // _CAPD_DIFFALGEBRA_CURVE_H_

