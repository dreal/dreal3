/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file algebraicOperations.h
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




#ifndef _CAPD_VECTALG_ALGEBRAICOPERATIONS_H_ 
#define _CAPD_VECTALG_ALGEBRAICOPERATIONS_H_ 

#include <stdexcept>
#include "capd/auxil/minmax.h"

inline double nonnegativePart(double x){
  return capd::abs(x);
}

inline double nonnegativePart(long double x){
  return capd::abs(x);
}

inline double nonnegativePart(int x){
  return capd::abs(x);
}



namespace capd{
namespace vectalg{

/// Assign zero to each coordinate
template<typename Object>
void clear(Object& u);

/// Computes euclidean norm of any vector
template<typename Object>
typename Object::ScalarType euclNorm(const Object& u);

/// normalize a vector with respect to euclidean norm
/// if impossible returns false
template<typename Object>
bool normalize(Object& u);

//------------------ unary arithmetic operations ------------------//

template<typename ResultType, typename Object>
ResultType absoluteValue(const Object& v);


template<typename ResultType, typename Object>
ResultType unaryMinus(const Object& v);

//-----------------------arithmetic operations----------------------//
/**
  this procedure can be use to add two vector-like objects:
  - vectors, matrices, references to columns or rows of matrix
  - higher dimensional containers
  result = v1 + v2
*/
template<typename ResultType, typename T1, typename T2>
void addObjects(const T1& v1,const T2& v2, ResultType& result);

template<typename ResultType, typename T1, typename T2>
inline
ResultType addObjects(const T1& v1,const T2& v2)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("capd::vectalg::addObjects: Incompatible dimensions");
  ResultType result(v1.dimension(),true);
  addObjects(v1,v2,result);
  return result;
}


/**
  this procedure can be use to subtract two vector-like objects:
  - vectors, matrices, references to columns or rows of matrix
  - higher dimensional containers
  result = v1 - v2
*/
template<typename ResultType, typename T1, typename T2>
void subtractObjects(const T1& v1,const T2& v2, ResultType& result);

template<typename ResultType, typename T1, typename T2>
inline
ResultType subtractObjects(const T1& v1,const T2& v2)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("capd::vectalg::addObjects: Incompatible dimensions");
  ResultType result(v1.dimension(),true);
  subtractObjects(v1,v2,result);
  return result;
}

/**
  this procedure can be use to compute scalar product of two vector-like objects:
  - vectors, matrices, references to columns or rows of matrix
  - vectors of partial derivatives from higher order containers
  result = v1 * v2
*/
template<typename T1, typename T2>
typename T1::ScalarType scalarProduct(const T1& v1,const T2& v2);

/**
  this procedure can be use to multiply by a scalar any element of vector-like objects
  as a result we may obtain object of different type,
    multiplication of column of matrix and scalar gives vector
  result = v * s
*/
template<typename ResultType, typename Object, typename FactorType>
ResultType multiplyObjectScalar(const Object& v,const FactorType& s);

/**
  this procedure can be use to divide by a scalar any element of vector-like objects
  as a result we may obtain object of different type,
    dividing of column of matrix by scalar gives vector
  result = v / s
*/
template<typename ResultType, typename Object, typename FactorType>
ResultType divideObjectScalar(const Object& v,const FactorType& s);

/**
  this procedure can be use to add a scalar to any element of vector-like objects
  result[i] = v[i] + s
*/
template<typename ResultType, typename Object, typename FactorType>
ResultType addObjectScalar(const Object& v,const FactorType& s);

/**
  this procedure can be used to substract a scalar from any element of vector-like objects
  result[i] = v[i] - s
*/
template<typename ResultType, typename Object, typename FactorType>
ResultType subtractObjectScalar(const Object& v,const FactorType& s);

/**
  this procedure realizes multiplication of matrix-like object by vector-like object
  result = m*v
*/
template<typename ResultType, typename MatrixType, typename VectorType>
void matrixByVector(const MatrixType& m,const VectorType& u, ResultType& result);

template<typename ResultType, typename MatrixType, typename VectorType>
inline
ResultType matrixByVector(const MatrixType& m,const VectorType& u)
{
  ResultType result(m.numberOfRows(),true);
  if(m.numberOfColumns()!=u.dimension())
    throw std::range_error("operator Matrix*Vector: incompatible dimensions");
  matrixByVector(m,u,result);
  return result;
}

/**
  this procedure realizes multiplication of two matrix-like objects
  result = m1*m2
*/
template<typename ResultType, typename Matrix1, typename Matrix2>
void matrixByMatrix(const Matrix1& a1, const Matrix2& a2, ResultType& result);

template<typename ResultType, typename Matrix1, typename Matrix2>
inline
ResultType matrixByMatrix(const Matrix1& a1, const Matrix2& a2)
{
  ResultType result(a1.numberOfRows(),a2.numberOfColumns(),true);
  if(a1.numberOfColumns()!=a2.numberOfRows())
    throw std::range_error("operator capd::vectalg::matrixByMatrix: incompatible matrix dimensions");
  matrixByMatrix(a1,a2,result);
  return result;
}

//----------------------assignments - objects---------------------------//

/**
  this procedure can be use to assign one vector-like objects
  from the other. 
  u = v
*/
template<typename T1, typename T2>
T1& assignObjectObject(T1& u, const T2& v);

/**
  this procedure can be use to add of two vector-like objects
  result is stored in the first argument
  u += v
*/
template<typename T1, typename T2>
T1& addAssignObjectObject(T1& u, const T2& v);

/**
  this procedure can be use to subtract of two vector-like objects
  result is stored in the first argument
  u -= v
*/
template<typename T1, typename T2>
T1& subtractAssignObjectObject(T1& u, const T2& v);

//----------------------assignments - Scalars---------------------------//

/**
  this procedure can be use to assign each element of a vector-like object
  to be equal to a given scalar
  u[i] = s
*/
template<typename Object,typename Scalar>
Object& assignFromScalar(Object& u, const Scalar& s);

/**
  this procedure can be use to add a scalar to each element of a vector-like object
  u[i] += s
*/
template<typename Object,typename Scalar>
Object& addAssignObjectScalar(Object& u, const Scalar& s);

/**
  this procedure can be use to subtract a scalar from each element of a vector-like object
  u[i] -= s
*/
template<typename Object,typename Scalar>
Object& subtractAssignObjectScalar(Object& u, const Scalar& s);

/**
  this procedure can be use to multiply by a scalar each element of a vector-like object
  u[i] *= s
*/
template<typename Object,typename Scalar>
Object& multiplyAssignObjectScalar(Object& u, const Scalar& s);

/**
  this procedure can be use to multiply by a scalar each element of a vector-like object
  and then add compoent-wise elements of second vector-like object
  u[i] = u[i]*s+v[i]
*/
template<typename Object, typename Object2, typename Scalar>
Object& multiplyAssignObjectScalarAddObject(Object& u, const Scalar& s, const Object2& v);

/**
  this procedure can be use to divide by a scalar any element of two vector-like objects
  u[i] /= s
*/
template<typename Object,typename Scalar>
Object& divideAssignObjectScalar(Object& u, const Scalar& s);

//-------coord-wise inequalities - true if true for each coord---------//

template<typename T1,typename T2>
bool lessThan (const T1& v1, const T2& v2);

template<typename T1,typename T2>
bool greaterThan (const T1& v1, const T2& v2);

template<typename T1,typename T2>
bool lessEqual (const T1& v1, const T2& v2);

template<typename T1,typename T2>
bool greaterEqual (const T1& v1, const T2& v2);

// ---------------------------------------- equality and not equality --------------------

template<typename T1,typename T2>
bool equal (const T1& v1, const T2& v2);

template<typename T1,typename T2>
bool notEqual (const T1& v1, const T2& v2)
{
  return ! equal(v1,v2);
}


}} // end of namespace capd::vectalg

#endif // _CAPD_VECTALG_ALGEBRAICOPERATIONS_H_ 

/// @}
