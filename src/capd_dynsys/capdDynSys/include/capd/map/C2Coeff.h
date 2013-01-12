/// @addtogroup map
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file C2Coeff.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* Author: Daniel Wilczak  2006 */

#ifndef _CAPD_MAP_C2COEFF_H_ 
#define _CAPD_MAP_C2COEFF_H_ 

#include "capd/vectalg/Matrix.h"

namespace capd{
namespace map{

template<typename Scalar>
class C2Coeff
{
  public:
  typedef Scalar ScalarType;
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;
  typedef C2Coeff ContainerType;

  // a value of the function \partial^2f_i/{\partial j\partial k}
  ScalarType& operator()(int i, int j, int k);
  const ScalarType& operator()(int i, int j, int k) const;
  ScalarType& operator[](int);
  const ScalarType& operator[](int) const;

  C2Coeff();
  C2Coeff(int dim);
  C2Coeff(const C2Coeff& s);
  C2Coeff& operator=(const C2Coeff& s);
  C2Coeff& operator+=(const C2Coeff& s);
  ~C2Coeff();

  int dimension() const;
  void* operator new[](size_t sizeOfData);
  void* operator new[](size_t sizeOfData, int newDefaultDim);
  iterator begin() { return data; }
  iterator end()   { return iterator(data+dim*dim*(1+dim)/2); }
  const_iterator begin() const { return const_iterator(data); }
  const_iterator end() const   { return const_iterator(data+dim*dim*(1+dim)/2); }
  void clear();
   
protected:
  ScalarType *data;
  int dim;
  static int defaultDim;
}; // the end of class C2Coeff


template <typename ScalarType,int d>
C2Coeff<ScalarType> operator*(const capd::vectalg::Matrix<ScalarType,d,d>& m, const C2Coeff<ScalarType>& c2);

// ------------------- inline definitions -------------------

template<typename ScalarType>
inline C2Coeff<ScalarType>::C2Coeff()
{
  dim = defaultDim;
  data = new ScalarType[dim*dim*(1+dim)/2];
}

template<typename ScalarType>
inline C2Coeff<ScalarType>::C2Coeff(int a_dim)
{
  dim = a_dim;
  data = new ScalarType[dim*dim*(1+dim)/2];
}

template<typename ScalarType>
inline C2Coeff<ScalarType>::~C2Coeff()
{
  delete []data;
}

template<typename ScalarType>
inline int C2Coeff<ScalarType>::dimension() const
{
  return dim;
}

template<typename ScalarType>
inline void* C2Coeff<ScalarType>::operator new[](size_t sizeOfData)
{
  return ::operator new[](sizeOfData);
}

template<typename ScalarType>
inline void* C2Coeff<ScalarType>::operator new[](size_t sizeOfData, int newDim)
{
  defaultDim = newDim;
  return ::operator new[](sizeOfData);
}

template<typename ScalarType>
inline ScalarType& C2Coeff<ScalarType>::operator[](int i)
{
  return data[i];
}

template<typename ScalarType>
inline const ScalarType& C2Coeff<ScalarType>::operator[](int i) const
{
  return data[i];
}

template<typename ScalarType>
inline ScalarType& C2Coeff<ScalarType>::operator()(int i, int j, int k)
{
  return k<=j ?
    data[i*dim*(dim+1)/2 + j*(j+1)/2 + k] : data[i*dim*(dim+1)/2 + k*(k+1)/2 + j];
}

template<typename ScalarType>
inline const ScalarType& C2Coeff<ScalarType>::operator()(int i, int j, int k) const
{
  return k<=j ?
    data[i*dim*(dim+1)/2 + j*(j+1)/2 + k] : data[i*dim*(dim+1)/2 + k*(k+1)/2 + j];
}

}} // namespace capd::map

#endif // _CAPD_MAP_C2COEFF_H_ 

/// @}
