/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ZVector.h
///
/// This file provides a class ZVector which is a facade of template
/// class Vector. The class realizes vectors of variable dimension
/// with integer coordinates
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



#ifndef _CAPD_ZVECTOR_H_
#define _CAPD_ZVECTOR_H_

#include "capd/vectalg/Vector.h"
#include "capd/vectalg/algebraicOperations.hpp"

namespace capd{


//########################### Vector template ################################//

class ZVector
{
public:
  typedef int ScalarType;
  typedef ZVector VectorType;
  typedef capd::vectalg::Vector<int,0> BaseVector;
  typedef BaseVector::ContainerType ContainerType;
  typedef ContainerType::iterator iterator;
  typedef ContainerType::const_iterator const_iterator;
  typedef capd::vectalg::Vector<int,0> intVectorType;

  ZVector(void){}
  explicit ZVector(int A_dimension) 
    : m_v(A_dimension) 
  {}
  
  ZVector(const int& x, const int& y,const int& z)
    : m_v(x,y,z)
  {}
  
  ZVector(int dim,int tab[] ) 
    : m_v(dim,tab)
  {}
  
  ZVector(const ZVector& u)
    : m_v(u.m_v)
  {}

  ZVector(const BaseVector& u)
    : m_v(u)
  {}

  ZVector(int dim,bool b)
    : m_v(dim,b)
  {}

  void clear(void){
    m_v.clear();
  }

  // assignments - vectors
  ZVector& operator=  (const ZVector& v);      //assign a vector
  ZVector& operator+= (const ZVector& v);      //increase by a vector
  ZVector& operator-= (const ZVector& v);      //decrease by a vector

  // assignments - Scalars
  ZVector& operator=  (const int s);       //assign a Scalar
  ZVector& operator+= (const int s);       //increase by a Scalar
  ZVector& operator-= (const int s);       //decrease by a Scalar
  ZVector& operator*= (const int s);       //rescale by multiplying
  ZVector& operator/= (const int s);       //rescale by dividing

  int dimension() const{
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
  int euclNorm(void) const{
    return m_v.euclNorm();
  }
  //if possible vector is normalized and true is returned. Otherwise false is returned.
  bool normalize(void){
    return m_v.normalize();
  }

  void sorting_permutation(intVectorType& perm){
    m_v.sorting_permutation(perm);
  }

  int& operator[](int i){
    return m_v[i];
  }

  const int& operator[](int i) const{
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
}; // end of class ZVector

// ---------------------------------------------------------------------------------------

inline std::ostream& operator<<(std::ostream& out, const ZVector& v){
  return out << v.m_v;
}

inline std::istream& operator>>(std::istream& inp, ZVector& v){
  return inp >> v.m_v;
}

inline ZVector abs(const ZVector& v){
  return capd::vectalg::absoluteValue<ZVector> (v);
}

inline ZVector operator-(const ZVector& v){
  return capd::vectalg::unaryMinus<ZVector>(v);
}

inline ZVector operator+(const ZVector& v1,const ZVector& v2){
  return capd::vectalg::addObjects<ZVector>(v1,v2);  
}

inline ZVector operator-(const ZVector& v1,const ZVector& v2){
  return capd::vectalg::subtractObjects<ZVector>(v1,v2);  
}

inline int operator*(const ZVector& v1,const ZVector& v2){
  return capd::vectalg::scalarProduct<ZVector>(v1,v2);
}

inline ZVector operator+(const ZVector& v, const int s){
  return capd::vectalg::addObjectScalar<ZVector>(v,s);
}

inline ZVector operator-(const ZVector& v,const int s){
  return capd::vectalg::subtractObjectScalar<ZVector>(v,s);
}

inline ZVector operator*(const ZVector& v, const int s){
  return capd::vectalg::multiplyObjectScalar<ZVector>(v,s);
}


inline ZVector operator*(const int s, const ZVector& v){
  return capd::vectalg::multiplyObjectScalar<ZVector>(v,s);
}

inline ZVector operator/(const ZVector& v, const int s){
  return capd::vectalg::divideObjectScalar<ZVector>(v,s);
}

inline ZVector& ZVector::operator=(const ZVector& v){
  m_v = v.m_v;
  return *this;
}

inline ZVector& ZVector::operator+=(const ZVector& v){
  return capd::vectalg::addAssignObjectObject(*this,v);
}

inline ZVector& ZVector::operator-=(const ZVector& v){
  return capd::vectalg::subtractAssignObjectObject(*this,v);
}

inline ZVector& ZVector::operator=(const int s){
  return capd::vectalg::assignFromScalar(*this,s);
}

inline ZVector& ZVector::operator+=(const int s){
  return capd::vectalg::addAssignObjectScalar(*this,s);
}

inline ZVector& ZVector::operator-=(const int s){
  return capd::vectalg::subtractAssignObjectScalar(*this,s);
}

inline ZVector& ZVector::operator*=(const int s){
  return capd::vectalg::multiplyAssignObjectScalar(*this,s);
}

inline ZVector& ZVector::operator/=(const int s){
  return capd::vectalg::divideAssignObjectScalar(*this,s);
}

inline bool operator< (const ZVector& v1, const ZVector& v2){
  return capd::vectalg::lessThan(v1,v2);
}

inline bool operator> (const ZVector& v1, const ZVector& v2){
  return capd::vectalg::greaterThan(v1,v2);
}

inline bool operator<= (const ZVector& v1, const ZVector& v2){
  return capd::vectalg::lessEqual(v1,v2);
}


inline bool operator>= (const ZVector& v1, const ZVector& v2){
  return capd::vectalg::greaterEqual(v1,v2);
}

// ----------------------------------- equality --------------------------------------

inline bool operator== (const ZVector& v1, const ZVector& v2){
  return capd::vectalg::equal(v1,v2);
}


inline bool operator!= (const ZVector& v1, const ZVector& v2){
  return capd::vectalg::notEqual(v1,v2);
} 

} // namespace capd::vectalg

#endif // _CAPD_ZVECTOR_H_

/// @}

