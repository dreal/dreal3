//////////////////////////////////////////////////////////////////////////////// @file Curve.hpp////// @author Daniel Wilczak, Tomasz Kapela/////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2000-2005 by the CAPD Group.//// This file constitutes a part of the CAPD library,// distributed under the terms of the GNU General Public License.// Consult  http://capd.wsb-nlu.edu.pl/ for details.
#ifndef _CAPD_DIFFALGEBRA_CURVE_HPP_
#define _CAPD_DIFFALGEBRA_CURVE_HPP_#include "capd/diffAlgebra/Curve.h"

namespace capd{namespace diffAlgebra{template<class MatrixT>Curve<MatrixT>::Curve(Real left, Real right, int dimension, int order)  : m_left(left), m_right(right), m_order(order), m_allocatedOrder(0), m_dimension(dimension){  this->allocate();}
template<class MatrixT>Curve<MatrixT>::Curve(const Curve& c)  : m_left(c.m_left), m_right(c.m_right), m_order(c.m_order), m_allocatedOrder(0), m_dimension(c.m_dimension){  this->allocate();  this->copyData(c);}
template<class MatrixT>Curve<MatrixT>& Curve<MatrixT>::operator=(const Curve& c){  if(&c == this)    return *this;  this->deallocate();  this->m_dimension = c.m_dimension;  this->m_order = c.m_order;  this->m_left = c.m_left;  this->m_right = c.m_right;  this->allocate();  this->copyData(c);  return *this;    }
template<class MatrixT>void Curve<MatrixT>::setOrder(int order) {  if(order==this->m_order)    return;  if(order> m_allocatedOrder) {    this->deallocate();    this->m_order = order;    this->allocate();  } else {    this->m_order = order;  }}
template<class MatrixT>Curve<MatrixT> Curve<MatrixT>::derivative() const {  typedef typename TypeTraits<ScalarType>::Real Real;  Curve result(this->m_left, this->m_right, this->m_dimension, this->m_order-1);  for(int i=0;i<=this->m_order;++i){    result.m_coefficientsAtCenter[i] = Real(i+1)*this->m_coefficientsAtCenter[i+1];    result.m_coefficients[i] = Real(i+1)*this->m_coefficients[i+1];    result.m_remainderCoefficients[i] = Real(i+1)*this->m_remainderCoefficients[i+1];
    result.m_matrixCoefficients[i] = ScalarType(i+1)*this->m_matrixCoefficients[i+1];    result.m_matrixRemainderCoefficients[i] = ScalarType(i+1)*this->m_matrixRemainderCoefficients[i+1];  }  return result;}
template<class MatrixT>Curve<MatrixT>::~Curve(){  this->deallocate();}
template<class MatrixT>void Curve<MatrixT>::clearCoefficients(){  for(int i=0;i<=this->m_order+1;++i){    this->m_coefficientsAtCenter[i].clear();    this->m_coefficients[i].clear();    this->m_remainderCoefficients[i].clear();
    this->m_matrixCoefficients[i].clear();    this->m_matrixRemainderCoefficients[i].clear();  }}template<class MatrixT>typename Curve<MatrixT>::VectorType Curve<MatrixT>::operator()(const ScalarType& h) const {  if(capd::TypeTraits<ScalarType>::isInterval) {    if(!(h>=this->m_left) || !(h<=this->m_right))
      throw std::domain_error("capd::diffAlgebra::Curve error - requested argument is out of domain");
    VectorType phi = this->m_coefficientsAtCenter[this->m_order];
    MatrixType jacPhi = this->m_matrixCoefficients[this->m_order];
    for(int i=this->m_order-1;i>=0;--i) {
      phi = phi*h + this->m_coefficientsAtCenter[i];
      jacPhi = jacPhi*h + this->m_matrixCoefficients[i];
    }
    VectorType rem = power(h,this->m_order+1)*this->m_remainderCoefficients[this->m_order+1];
    return phi + jacPhi*( *(this->m_coefficients) - *(this->m_coefficientsAtCenter)) + rem;  } else {    // Non-rigorous version    if(!(h>=this->m_left) || !(h<=this->m_right))      throw std::domain_error("capd::diffAlgebra::Curve error - requested argument is out of domain");    VectorType phi = this->m_coefficientsAtCenter[this->m_order];    for(int i=this->m_order-1;i>=0;--i){      phi = phi*h + this->m_coefficientsAtCenter[i];    }    return phi;  }
}  // operator()
template<class MatrixT>MatrixT Curve<MatrixT>::operator[](const ScalarType& h) const {  if(!(h>=this->m_left) || !(h<=this->m_right))    throw std::domain_error("capd::diffAlgebra::Curve error - requested argument is out of domain");
  MatrixType jacPhi = this->m_matrixCoefficients[this->m_order];  for(int i=this->m_order-1;i>=0;--i){    jacPhi = jacPhi*h + this->m_matrixCoefficients[i];  }  if(capd::TypeTraits<ScalarType>::isInterval) {
    MatrixType jacRem = power(h,this->m_order+1)*this->m_matrixRemainderCoefficients[this->m_order+1];    return jacPhi+jacRem;  } else {    return jacPhi;  }} // operator[]
template<class MatrixT>void Curve<MatrixT>::allocate(){
  m_coefficientsAtCenter = new (this->m_dimension) VectorType[this->m_order+2];  m_coefficients = new (this->m_dimension) VectorType[this->m_order+2];  m_remainderCoefficients = new (this->m_dimension) VectorType[this->m_order+2];  m_matrixCoefficients = new (this->m_dimension,this->m_dimension) MatrixType[this->m_order+2];  m_matrixRemainderCoefficients = new (this->m_dimension,this->m_dimension) MatrixType[this->m_order+2];  this->m_allocatedOrder = m_order;}
template<class MatrixT>void Curve<MatrixT>::deallocate(){
  delete [] m_coefficientsAtCenter;  delete [] m_coefficients;  delete [] m_remainderCoefficients;  delete [] m_matrixCoefficients;  delete [] m_matrixRemainderCoefficients; }
template<class MatrixT>void Curve<MatrixT>::copyData(const Curve& c){
  for(int i=0;i<=this->m_order+1;++i){    this->m_coefficientsAtCenter[i] = c.m_coefficientsAtCenter[i];    this->m_coefficients[i] = c.m_coefficients[i];    this->m_remainderCoefficients[i] = c.m_remainderCoefficients[i];    this->m_matrixCoefficients[i] = c.m_matrixCoefficients[i];    this->m_matrixRemainderCoefficients[i] = c.m_matrixRemainderCoefficients[i];  }}
}} // namespace capd::diffAlgebra

#endif // _CAPD_DIFFALGEBRA_CURVE_HPP_
