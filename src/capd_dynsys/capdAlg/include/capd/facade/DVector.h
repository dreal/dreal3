/////////////////////////////////////////////////////////////////////////////
/// @file DVector.h
///
/// This file provides a class DVector which is a facade of template
/// class Vector. The class realizes vectors of variable dimension
/// with double precision coordinates
///
/// The main intention of providing this code is to make simpler usage of
/// template classes
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _CAPD_FACADE_DVECTOR_H_
#define _CAPD_FACADE_DVECTOR_H_

#include "capd/basicalg/doubleFun.h"
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/RowVector.h"
#include "capd/vectalg/ColumnVector.h"
#include "capd/vectalg/algebraicOperations.hpp"

namespace capd{
namespace facade{


//########################### Vector template ################################//

class DVector
{
public:

  typedef double ScalarType;
  typedef DVector VectorType;
  typedef capd::vectalg::Vector<double,0> BaseVector;
  typedef BaseVector::ContainerType ContainerType;
  typedef ContainerType::iterator iterator;
  typedef ContainerType::const_iterator const_iterator;
  typedef capd::vectalg::RowVector<double,0> RowVectorType;
  typedef capd::vectalg::ColumnVector<double,0> ColumnVectorType;

  const static int csDim = BaseVector::csDim;

  template<typename U>
  struct rebind {
      typedef capd::vectalg::Vector<U,0> other;
  };

  DVector(void){}
  explicit DVector(int A_dimension) 
    : m_v(A_dimension) 
  {}
  
  DVector(const double& x, const double& y,const double& z)
    : m_v(x,y,z)
  {}
  
  DVector(int dim,double tab[] ) 
    : m_v(dim,tab)
  {}
  
  DVector(const DVector& u)
    : m_v(u.m_v)
  {}
  
  DVector(const BaseVector& u)
    : m_v(u)
  {}
  
  DVector(const RowVectorType& u)
    : m_v(u)
  {}

  DVector(const ColumnVectorType& u)
    : m_v(u)
  {}

  DVector(int dim,bool b)
    : m_v(dim,b)
  {}

  void clear(void){
    m_v.clear();
  }

  // assignments - vectors
  DVector& operator=  (const BaseVector& v);      //assign a vector
  DVector& operator=  (const RowVectorType& v);      //assign a vector
  DVector& operator=  (const ColumnVectorType& v);      //assign a vector
  DVector& operator=  (const DVector& v);      //assign a vector
  DVector& operator+= (const DVector& v);      //increase by a vector
  DVector& operator-= (const DVector& v);      //decrease by a vector

  // assignments - Scalars
  DVector& operator=  (const double& s);       //assign a Scalar
  DVector& operator+= (const double& s);       //increase by a Scalar
  DVector& operator-= (const double& s);       //decrease by a Scalar
  DVector& operator*= (const double& s);       //rescale by multiplying
  DVector& operator/= (const double& s);       //rescale by dividing

  int dimension() const{
    return m_v.dimension();
  }
  int size() const{
     return m_v.dimension();
  }
  iterator begin(){
    return m_v.begin();
  }
  iterator end(){
    return m_v.end();
  }
  
  const_iterator begin() const{
    return m_v.begin();
  }
  const_iterator end() const{
    return m_v.end();
  }

  void resize(int s){
    m_v.resize(s);
  }

  // Euclidean norm
  double euclNorm(void) const{
    return m_v.euclNorm();
  }
  //if possible vector is normalized and true is returned. Otherwise false is returned.
  bool normalize(void){
    return m_v.normalize();
  }

  void sorting_permutation(rebind<int>::other& perm){
    m_v.sorting_permutation(perm);
  }

  double& operator[](int i){
    return m_v[i];
  }

  const double& operator[](int i) const{
    return m_v[i];
  }

  void* operator new[](size_t sizeOfData){
    return ::operator new[](sizeOfData);
  }

  void* operator new[](size_t sizeOfData,int newSize)
  {
    BaseVector::setDefaultDimension(newSize);
    return ::operator new[](sizeOfData);
  }

  BaseVector m_v;
}; // end of class DVector

// ---------------------------------------------------------------------------------------

inline std::ostream& operator<<(std::ostream& out, const DVector& v){
  return out << v.m_v;
}

inline std::istream& operator>>(std::istream& inp, DVector& v){
  return inp >> v.m_v;
}

inline DVector abs(const DVector& v){
  return capd::vectalg::absoluteValue<DVector> (v);
}

inline DVector operator-(const DVector& v){
  return capd::vectalg::unaryMinus<DVector>(v);
}

inline DVector operator+(const DVector& v1,const DVector& v2){
  return capd::vectalg::addObjects<DVector>(v1,v2);  
}

inline DVector operator-(const DVector& v1,const DVector& v2){
  return capd::vectalg::subtractObjects<DVector>(v1,v2);  
}

inline double operator*(const DVector& v1,const DVector& v2){
  return capd::vectalg::scalarProduct<DVector>(v1,v2);
}

inline DVector operator+(const DVector& v, const double& s){
  return capd::vectalg::addObjectScalar<DVector>(v,s);
}

inline DVector operator-(const DVector& v,const double& s){
  return capd::vectalg::subtractObjectScalar<DVector>(v,s);
}

inline DVector operator*(const DVector& v, const double s){
  return capd::vectalg::multiplyObjectScalar<DVector>(v,s);
}

inline DVector operator*(const DVector& v, const int s){
  return capd::vectalg::multiplyObjectScalar<DVector>(v,s);
}

inline DVector operator*(const double s, const DVector& v){
  return capd::vectalg::multiplyObjectScalar<DVector>(v,s);
}

inline DVector operator*(const int s, const DVector& v){
  return capd::vectalg::multiplyObjectScalar<DVector>(v,s);
}

inline DVector operator/(const DVector& v, const int s){
  return capd::vectalg::divideObjectScalar<DVector>(v,s);
}

inline DVector operator/(const DVector& v, const double s){
  return capd::vectalg::divideObjectScalar<DVector>(v,s);
}

inline DVector& DVector::operator=(const DVector& v){
  m_v = v.m_v;
  return *this;
}

inline DVector& DVector::operator=(const BaseVector& v){
  m_v = v;
  return *this;
}

inline DVector& DVector::operator=(const RowVectorType& v){
  m_v = v;
  return *this;
}

inline DVector& DVector::operator=(const ColumnVectorType& v){
  m_v = v;
  return *this;
}

inline DVector& DVector::operator+=(const DVector& v){
  return capd::vectalg::addAssignObjectObject(*this,v);
}

inline DVector& DVector::operator-=(const DVector& v){
  return capd::vectalg::subtractAssignObjectObject(*this,v);
}

inline DVector& DVector::operator=(const double& s){
  return capd::vectalg::assignFromScalar(*this,s);
}

inline DVector& DVector::operator+=(const double& s){
  return capd::vectalg::addAssignObjectScalar(*this,s);
}

inline DVector& DVector::operator-=(const double& s){
  return capd::vectalg::subtractAssignObjectScalar(*this,s);
}

inline DVector& DVector::operator*=(const double& s){
  return capd::vectalg::multiplyAssignObjectScalar(*this,s);
}

inline DVector& DVector::operator/=(const double& s){
  return capd::vectalg::divideAssignObjectScalar(*this,s);
}

inline bool operator< (const DVector& v1, const DVector& v2){
  return capd::vectalg::lessThan(v1,v2);
}

inline bool operator> (const DVector& v1, const DVector& v2){
  return capd::vectalg::greaterThan(v1,v2);
}

inline bool operator<= (const DVector& v1, const DVector& v2){
  return capd::vectalg::lessEqual(v1,v2);
}


inline bool operator>= (const DVector& v1, const DVector& v2){
  return capd::vectalg::greaterEqual(v1,v2);
}

// ----------------------------------- equality --------------------------------------

inline bool operator== (const DVector& v1, const DVector& v2){
  return capd::vectalg::equal(v1,v2);
}


inline bool operator!= (const DVector& v1, const DVector& v2){
  return capd::vectalg::notEqual(v1,v2);
} 

}} // the end of the namespace capd::facade

#endif // _CAPD_FACADE_DVECTOR_H_


