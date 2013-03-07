/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file algebraicOperations.hpp
///
/// This file provides an algebraic operation which may be implemented on the container level
/// such as addition of some objects
///
/// Constraints on any type which appears in these algorithms:
/// - public typedef ScalarType
/// - public types const_iterator and iterator and corresponding functions begin(), end()
/// - public const function dimension() which returns an object which can be used to initialize other objects
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 




#ifndef _CAPD_VECTALG_ALGEBRAICOPERATIONS_HPP_ 
#define _CAPD_VECTALG_ALGEBRAICOPERATIONS_HPP_ 

#include <stdexcept>
#include "capd/auxil/minmax.h"
#include "capd/vectalg/algebraicOperations.h"
#include "capd/basicalg/TypeTraits.h"

namespace capd{
namespace vectalg{


/// Assign zero to each coordinate
template<typename Object>
void clear(Object& u){
  typename Object::iterator b=u.begin(), e=u.end();
  while(b!=e)
  {
    *b = TypeTraits<typename Object::ScalarType>::zero();
    ++b;
  }
}

/// Computes euclidean norm of any vector
template<typename Object>
typename Object::ScalarType euclNorm(const Object& u){
  typedef typename Object::ScalarType Scalar;
  Scalar sum = TypeTraits<Scalar>::zero();
  typename Object::const_iterator b=u.begin(), e=u.end();
  while(b!=e)
  {
    sum += static_cast<Scalar>(power(*b,2));
    ++b;
  }
  return Scalar(sqrt(nonnegativePart(sum)));
}

/// normalize a vector with respect to euclidean norm
/// if impossible returns false
template<typename Object>
bool normalize(Object& u){
  typedef typename Object::ScalarType Scalar;
  Scalar n;
  if( ! (( n=euclNorm(u)) > 0.0) )
  {
    return false;
  }else{
    typename Object::iterator b=u.begin(), e=u.end();
    while(b!=e)
    {
      *b /=n;
      ++b;
    }
    return true;
  }
}

//------------------ unary arithmetic operations ------------------//

template<typename ResultType, typename Object>
ResultType absoluteValue(const Object& v)
{
  ResultType result(v.dimension(),true);
  typename ResultType::iterator b=result.begin(), e=result.end();
  typename Object::const_iterator i=v.begin();
  while(b!=e)
  {
    *b = capd::abs(*i);
    ++b;
    ++i;
  }
  return result;
}


template<typename ResultType, typename Object>
ResultType unaryMinus(const Object& v)
{
  ResultType result(v.dimension(),true);
  typename ResultType::iterator b=result.begin(), e=result.end();
  typename Object::const_iterator i=v.begin();
  while(b!=e)
  {
    *b = -(*i);
    ++b;
    ++i;
  }
  return result;
}

//-----------------------arithmetic operations----------------------//
/**
  this procedure can be use to add two vector-like objects:
  - vectors, matrices, references to columns or rows of matrix
  - higher dimensional containers
  result = v1 + v2
*/
template<typename ResultType, typename T1, typename T2>
void addObjects(const T1& v1,const T2& v2, ResultType& result)
{
  typename ResultType::iterator b=result.begin(), e=result.end();
  typename T1::const_iterator b1=v1.begin();
  typename T2::const_iterator b2=v2.begin();
  while(b!=e)
  {
    *b = (*b1) + (*b2);
    ++b;
    ++b1;
    ++b2;
  }
}


/**
  this procedure can be use to subtract two vector-like objects:
  - vectors, matrices, references to columns or rows of matrix
  - higher dimensional containers
  result = v1 - v2
*/
template<typename ResultType, typename T1, typename T2>
void subtractObjects(const T1& v1,const T2& v2, ResultType& result)
{
  typename ResultType::iterator b=result.begin(), e=result.end();
  typename T1::const_iterator b1=v1.begin();
  typename T2::const_iterator b2=v2.begin();
  while(b!=e)
  {
    *b = (*b1) - (*b2);
    ++b;
    ++b1;
    ++b2;
  }
}

/**
  this procedure can be use to compute scalar product of two vector-like objects:
  - vectors, matrices, references to columns or rows of matrix
  - vectors of partial derivatives from higher order containers
  result = v1 * v2
*/
template<typename T1, typename T2>
typename T1::ScalarType scalarProduct(const T1& v1,const T2& v2)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("capd::vectalg::scalarProduct: Incompatible dimensions");
  typename T1::ScalarType result(0);
  typename T1::const_iterator b1=v1.begin();
  typename T2::const_iterator b2=v2.begin(), e2=v2.end();
  while(b2!=e2)
  {
    result += (*b1) * (*b2);
    ++b1;
    ++b2;
  }
  return result;
}


/**
  this procedure can be use to multiply by a scalar any element of vector-like objects
  as a result we may obtain object of different type,
    multiplication of column of matrix and scalar gives vector
  result = v * s
*/
template<typename ResultType, typename Object, typename FactorType>
void multiplyObjectScalar(const Object& v,const FactorType& s, ResultType& result)
{
  typename Object::const_iterator b=v.begin(), e=v.end();
  typename ResultType::iterator i=result.begin();
  while(b!=e)
  {
    *i = (*b) * s;
    ++i;
    ++b;
  }
}

/**
  this procedure can be use to multiply by a scalar any element of vector-like objects
  as a result we may obtain object of different type,
    multiplication of column of matrix and scalar gives vector
  result = v * s
*/
template<typename ResultType, typename Object, typename FactorType>
ResultType multiplyObjectScalar(const Object& v,const FactorType& s)
{
  ResultType result(v.dimension(),true);
  multiplyObjectScalar(v,s,result);
  return result;
}


/**
  this procedure can be use to divide by a scalar any element of vector-like objects
  as a result we may obtain object of different type,
    dividing of column of matrix by scalar gives vector
  result = v / s
*/
template<typename ResultType, typename Object, typename FactorType>
ResultType divideObjectScalar(const Object& v,const FactorType& s)
{
  ResultType result(v.dimension(),true);
  typename Object::const_iterator b=v.begin(), e=v.end();
  typename ResultType::iterator i=result.begin();
  while(b!=e)
  {
    *i = (*b) / s;
    ++i;
    ++b;
  }
  return result;
}


/**
  this procedure can be use to add a scalar to any element of vector-like objects
  result[i] = v[i] + s
*/
template<typename ResultType, typename Object, typename FactorType>
ResultType addObjectScalar(const Object& v,const FactorType& s)
{
  ResultType result(v.dimension(),true);
  typename Object::const_iterator b=v.begin(), e=v.end();
  typename ResultType::iterator i=result.begin();
  while(b!=e)
  {
    *i = (*b) + s;
    ++i;
    ++b;
  }
  return result;
}

/**
  this procedure can be use to subtract a scalar from any element of vector-like objects
  result[i] = v[i] - s
*/
template<typename ResultType, typename Object, typename FactorType>
ResultType subtractObjectScalar(const Object& v,const FactorType& s)
{
  ResultType result(v.dimension(),true);
  typename Object::const_iterator b=v.begin(), e=v.end();
  typename ResultType::iterator i=result.begin();
  while(b!=e)
  {
    *i = (*b) - s;
    ++i;
    ++b;
  }
  return result;
}

/**
  this procedure realizes multiplication of matrix-like object by vector-like object
  result = m*v
*/
template<typename ResultType, typename MatrixType, typename VectorType>
void matrixByVector(const MatrixType& m,const VectorType& u, ResultType& result){
  typename ResultType::iterator b=result.begin(), e=result.end();
  typename MatrixType::const_iterator i = m.begin();
  while(b!=e)
  {
    typename ResultType::ScalarType x = capd::TypeTraits<typename ResultType::ScalarType>::zero();
    typename VectorType::const_iterator bv=u.begin(), be=u.end();
    while(bv!=be)
    {
      x += (*bv) * (*i);
      ++bv;
      ++i;
    }
    *b=x;
    ++b;
  }
}


/**
  this procedure realizes multiplication of two matrix-like objects
  result = m1*m2
*/
template<typename ResultType, typename Matrix1, typename Matrix2>
void matrixByMatrix(const Matrix1& a1, const Matrix2& a2, ResultType& result)
{
  for(int i=0;i<result.numberOfColumns();++i)
  {
    typename ResultType::iterator b=result.begin()+i, e=result.end()+i;
    typename Matrix1::const_iterator j=a1.begin();
    while(b!=e)
    {
      typename Matrix2::const_iterator b1=a2.begin()+i, e1=a2.end()+i;
      typename ResultType::ScalarType x = TypeTraits<typename ResultType::ScalarType>::zero();
      while(b1!=e1)
      {
        x += (*j) * (*b1);
        ++j;
        b1+=a2.rowStride();
      }
      *b=x;
      b+=result.rowStride();
    }
  }
}

//----------------------assignments - objects---------------------------//

/**
  this procedure can be use to assign one vector-like objects
  from the other. 
  u = v
*/
template<typename T1, typename T2>
T1& assignObjectObject(T1& u, const T2& v){
  typename T1::iterator b=u.begin(), e=u.end();
  typename T2::const_iterator i = v.begin();
  while(b!=e)
  {
    *b = static_cast<typename T1::ScalarType>(*i);
    ++b;
    ++i;
  }
  return u;
}

/**
  this procedure can be use to add of two vector-like objects
  result is stored in the first argument
  u += v
*/
template<typename T1, typename T2>
T1& addAssignObjectObject(T1& u, const T2& v)
{
  if(u.dimension()!=v.dimension())
    throw std::range_error("capd::vectalg::addAssignObjectObject: Incompatible dimensions");
  typename T1::iterator i=u.begin();
  typename T2::const_iterator b=v.begin(), e=v.end();
  while(b!=e)
  {
    *i += *b;
    ++i;
    ++b;
  }
  return u;
}


/**
  this procedure can be use to subtract of two vector-like objects
  result is stored in the first argument
  u += v
*/
template<typename T1, typename T2>
T1& subtractAssignObjectObject(T1& u, const T2& v)
{
  if(u.dimension()!=v.dimension())
    throw std::range_error("capd::vectalg::subtractAssignObjectObject: Incompatible dimensions");
  typename T1::iterator i=u.begin();
  typename T2::const_iterator b=v.begin(), e=v.end();
  while(b!=e)
  {
    *i -= *b;
    ++i;
    ++b;
  }
  return u;
}

//----------------------assignments - Scalars---------------------------//

/**
  this procedure can be use to assign any element of two vector-like objects
  to be equal to a given scalar
  u[i] = s
*/
template<typename Object,typename Scalar>
Object& assignFromScalar(Object& u, const Scalar& s)
{
  typename Object::iterator b=u.begin(), e=u.end();
  while(b!=e)
  {
    *b = s;
    ++b;
  }
  return u;
}


/**
  this procedure can be use to add a scalar to any element of two vector-like objects
  u[i] += s
*/
template<typename Object,typename Scalar>
Object& addAssignObjectScalar(Object& u, const Scalar& s)
{
  typename Object::iterator b=u.begin(), e=u.end();
  while(b!=e)
  {
    *b += s;
    ++b;
  }
  return u;
}


/**
  this procedure can be use to subtract a scalar from any element of two vector-like objects
  u[i] -= s
*/
template<typename Object,typename Scalar>
Object& subtractAssignObjectScalar(Object& u, const Scalar& s)
{
  typename Object::iterator b=u.begin(), e=u.end();
  while(b!=e)
  {
    *b -= s;
    ++b;
  }
  return u;
}


/**
  this procedure can be use to multiply by a scalar any element of two vector-like objects
  u[i] *= s
*/
template<typename Object,typename Scalar>
Object& multiplyAssignObjectScalar(Object& u, const Scalar& s)
{
  typename Object::iterator b=u.begin(), e=u.end();
  while(b!=e)
  {
    *b *= s;
    ++b;
  }
  return u;
}

/**
  this procedure can be use to multiply by a scalar each element of a vector-like object
  and then add compoent-wise elements of second vector-like object
  u[i] = u[i]*s+v[i]
*/
template<typename Object, typename Object2, typename Scalar>
Object& multiplyAssignObjectScalarAddObject(Object& u, const Scalar& s, const Object2& v)
{
  typename Object::iterator b=u.begin(), e=u.end();
  typename Object2::const_iterator i = v.begin();
  while(b!=e)
  {
    *b = (*b)*s + (*i);
    ++b;
    ++i;
  }
  return u;
}


/**
  this procedure can be use to divide by a scalar any element of two vector-like objects
  u[i] /= s
*/
template<typename Object,typename Scalar>
Object& divideAssignObjectScalar(Object& u, const Scalar& s)
{
  typename Object::iterator b=u.begin(), e=u.end();
  while(b!=e)
  {
    *b /= s;
    ++b;
  }
  return u;
}


//-------coord-wise inequalities - true if true for each coord---------//

template<typename T1,typename T2>
bool lessThan (const T1& v1, const T2& v2)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("capd::vectalg::lessThan: Incompatible dimensions");
  typename T1::const_iterator b1=v1.begin(), e1=v1.end();
  typename T2::const_iterator b2=v2.begin();
  
  while(b1!=e1)
  {
    if(!(*b1 < *b2))
       return false;
    ++b1;
    ++b2;
  }
  return true;
}


template<typename T1,typename T2>
bool greaterThan (const T1& v1, const T2& v2)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("capd::vectalg::greaterThan: Incompatible dimensions");
  typename T1::const_iterator b1=v1.begin(), e1=v1.end();
  typename T2::const_iterator b2=v2.begin();
  
  while(b1!=e1)
  {
    if(!(*b1 > *b2))
       return false;
    ++b1;
    ++b2;
  }
  return true;
}


template<typename T1,typename T2>
bool lessEqual (const T1& v1, const T2& v2)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("capd::vectalg::lessEqual: Incompatible dimensions");
  typename T1::const_iterator b1=v1.begin(), e1=v1.end();
  typename T2::const_iterator b2=v2.begin();
  
  while(b1!=e1)
  {
    if(!(*b1 <= *b2))
       return false;
    ++b1;
    ++b2;
  }
  return true;
}


template<typename T1,typename T2>
bool greaterEqual (const T1& v1, const T2& v2)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("capd::vectalg::greaterEqual: Incompatible dimensions");
  typename T1::const_iterator b1=v1.begin(), e1=v1.end();
  typename T2::const_iterator b2=v2.begin();
  
  while(b1!=e1)
  {
    if(!(*b1 >= *b2))
       return false;
    ++b1;
    ++b2;
  }
  return true;
}

// ---------------------------------------- equality and not equality --------------------

template<typename T1,typename T2>
bool equal (const T1& v1, const T2& v2)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("capd::vectalg::equal: Incompatible dimensions");
  typename T1::const_iterator b1=v1.begin(), e1=v1.end();
  typename T2::const_iterator b2=v2.begin();
  
  while(b1!=e1)
  {
    if(!(*b1 == *b2))
       return false;
    ++b1;
    ++b2;
  }
  return true;
}


}} // end of namespace capd::vectalg

#endif // _CAPD_VECTALG_ALGEBRAICOPERATIONS_HPP_ 

/// @}
