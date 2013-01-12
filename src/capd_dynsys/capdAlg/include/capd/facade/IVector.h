/////////////////////////////////////////////////////////////////////////////
/// @file IVector.h
///
/// This file provides a class IVector which is a facade of template
/// class Vector. The class realizes vectors of variable dimension
/// with interval coordinates
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



#ifndef _CAPD_FACADE_IVECTOR_H_
#define _CAPD_FACADE_IVECTOR_H_

#include "capd/facade/DInterval.h"
#include "capd/facade/DVector.h"


#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/RowVector.h"
#include "capd/vectalg/ColumnVector.h"
#include "capd/vectalg/algebraicOperations.hpp"
#include "capd/vectalg/iobject.hpp"

namespace capd{
namespace facade{

// in the future we include here a fascade for intervals
// now is a simple typedef

//########################### Vector template ################################//

class IVector
{
public:
  typedef DInterval ScalarType;
  typedef IVector VectorType;
  typedef capd::vectalg::Vector<DInterval,0> BaseVector;
  typedef BaseVector::ContainerType ContainerType;
  typedef ContainerType::iterator iterator;
  typedef ContainerType::const_iterator const_iterator;
  typedef capd::vectalg::RowVector<DInterval,0> RowVectorType;
  typedef capd::vectalg::ColumnVector<DInterval,0> ColumnVectorType;

  template<typename U>
  struct rebind {
      typedef capd::vectalg::Vector<U,0> other;
  };

  IVector(void){}
  explicit IVector(int A_dimension)
    : m_v(A_dimension)
  {}

  IVector(const DInterval& x, const DInterval& y,const DInterval& z)
    : m_v(x,y,z)
  {}

  IVector(int dim,DInterval tab[] )
    : m_v(dim,tab)
  {}

  IVector(const IVector& u)
    : m_v(u.m_v)
  {}

  IVector(const BaseVector& u)
    : m_v(u)
  {}

  IVector(const RowVectorType& u)
    : m_v(u)
  {}

  IVector(const ColumnVectorType& u)
    : m_v(u)
  {}

  IVector(int dim,bool b)
    : m_v(dim,b)
  {}

  void clear(void){
    m_v.clear();
  }

  // assignments - vectors
  IVector& operator=  (const IVector& v);      //assign a vector
  IVector& operator=  (const BaseVector& v);      //assign a vector
  IVector& operator=  (const RowVectorType& v);      //assign a vector
  IVector& operator=  (const ColumnVectorType& v);      //assign a vector
  IVector& operator+= (const IVector& v);      //increase by a vector
  IVector& operator-= (const IVector& v);      //decrease by a vector

  // assignments - Scalars
  IVector& operator=  (const DInterval& s);       //assign a Scalar
  IVector& operator+= (const DInterval& s);       //increase by a Scalar
  IVector& operator-= (const DInterval& s);       //decrease by a Scalar
  IVector& operator*= (const DInterval& s);       //rescale by multiplying
  IVector& operator/= (const DInterval& s);       //rescale by dividing

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
  DInterval euclNorm(void) const{
    return m_v.euclNorm();
  }
  //if possible vector is normalized and true is returned. Otherwise false is returned.
  bool normalize(void){
    return m_v.normalize();
  }

  void sorting_permutation(rebind<int>::other& perm){
    m_v.sorting_permutation(perm);
  }

  DInterval& operator[](int i){
    return m_v[i];
  }

  const DInterval& operator[](int i) const{
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
  operator const BaseVector & () const{
    return m_v;
  }
  operator BaseVector & (){
      return m_v;
  }

 // TODO : m_v should be private
//  private:
  BaseVector m_v;
}; // end of class IVector

inline std::ostream& operator<<(std::ostream& out, const IVector& v){
  return out << v.m_v;
}

inline std::istream& operator>>(std::istream& inp, IVector& v){
  return inp >> v.m_v;
}

// ---------------------------------------------------------------- //
// general algorithms for vectors and matrices

inline void split(IVector& u, IVector& v){
  capd::vectalg::split(u,v);
}

inline void split(IVector &v, IVector& mid, IVector& r){
  capd::vectalg::split(v, mid, r);
}

inline void split(IVector &v, DVector& mid, IVector& r){
  capd::vectalg::split(v, mid, r);
}

inline bool subset(const IVector& u, const IVector& v){
  return capd::vectalg::subset(u,v);
}

inline bool subsetInterior(const IVector& u, const IVector& v){
  return capd::vectalg::subsetInterior(u,v);
}

inline bool intersection(const IVector& v1, const IVector& v2, IVector& result){
  return capd::vectalg::intersection(v1,v2,result);
}

// ---------------------------------------------------------------- //

inline IVector leftVector(const IVector& u){
  return capd::vectalg::leftVector(u);
}

inline IVector rightVector(const IVector& u){
  return capd::vectalg::rightVector(u);
}

inline DInterval size(const IVector& u){
  return capd::vectalg::size(u);
}

inline IVector intervalBall(const IVector& u, DInterval &r){
  IVector result;
  result.m_v = capd::vectalg::intervalBall(u.m_v,r);
  return result;
}


inline DInterval solveAffineInclusion(const IVector& a,const IVector& b,const IVector& c){
  return capd::vectalg::solveAffineInclusion(a.m_v,b.m_v,c.m_v);
}

inline DInterval solveAffineInclusion(const IVector& a,const IVector& b,const IVector& c, int p){
  return capd::vectalg::solveAffineInclusion(a.m_v,b.m_v,c.m_v,p);
}

inline IVector intervalHull(const IVector& u, const IVector& v){
  IVector result(u.dimension());
  result.m_v = capd::vectalg::intervalHull(u.m_v,v.m_v);
  return result;
}

inline IVector midVector(const IVector& u){
  IVector result(u.dimension());
  capd::vectalg::mid(u,result);
  return result;
}

inline IVector diam(const IVector& u){
  IVector result(u.dimension());
  result.m_v = capd::vectalg::diam(u.m_v);
  return result;
}

inline IVector intersection(const IVector&a, const IVector&b){
  IVector result(a.dimension());
  intersection(a.m_v,b.m_v,result.m_v);
  return result;
}

inline IVector abs(const IVector& v){
  return capd::vectalg::absoluteValue<IVector> (v);
}

inline IVector operator-(const IVector& v){
  return capd::vectalg::unaryMinus<IVector>(v);
}

inline IVector operator+(const IVector& v1,const IVector& v2){
  return capd::vectalg::addObjects<IVector>(v1,v2);
}

inline IVector operator-(const IVector& v1,const IVector& v2){
  return capd::vectalg::subtractObjects<IVector>(v1,v2);
}

inline DInterval operator*(const IVector& v1,const IVector& v2){
  return capd::vectalg::scalarProduct<IVector>(v1,v2);
}

inline IVector operator+(const IVector& v, const DInterval& s){
  return capd::vectalg::addObjectScalar<IVector>(v,s);
}

inline IVector operator-(const IVector& v,const DInterval& s){
  return capd::vectalg::subtractObjectScalar<IVector>(v,s);
}

inline IVector operator*(const IVector& v, const double s){
  return capd::vectalg::multiplyObjectScalar<IVector>(v,s);
}

inline IVector operator*(const IVector& v, const int s){
  return capd::vectalg::multiplyObjectScalar<IVector>(v,s);
}

inline IVector operator*(const IVector& v, const DInterval& s){
  return capd::vectalg::multiplyObjectScalar<IVector>(v,s);
}

inline IVector operator*(const double s, const IVector& v){
  return capd::vectalg::multiplyObjectScalar<IVector>(v,s);
}

inline IVector operator*(const int s, const IVector& v){
  return capd::vectalg::multiplyObjectScalar<IVector>(v,s);
}

inline IVector operator*(const DInterval& s, const IVector& v){
  return capd::vectalg::multiplyObjectScalar<IVector>(v,s);
}

inline IVector operator/(const IVector& v, const int s){
  return capd::vectalg::divideObjectScalar<IVector>(v,s);
}

inline IVector operator/(const IVector& v, const double s){
  return capd::vectalg::divideObjectScalar<IVector>(v,s);
}

inline IVector operator/(const IVector& v, const DInterval& s){
  return capd::vectalg::divideObjectScalar<IVector>(v,s);
}

inline IVector& IVector::operator=(const IVector& v){
  m_v = v.m_v;
  return *this;
}

inline IVector& IVector::operator=(const BaseVector& v){
  m_v = v;
  return *this;
}

inline IVector& IVector::operator=(const RowVectorType& v){
  m_v = v;
  return *this;
}

inline IVector& IVector::operator=(const ColumnVectorType& v){
  m_v = v;
  return *this;
}

inline IVector& IVector::operator+=(const IVector& v){
  return capd::vectalg::addAssignObjectObject(*this,v);
}

inline IVector& IVector::operator-=(const IVector& v){
  return capd::vectalg::subtractAssignObjectObject(*this,v);
}

inline IVector& IVector::operator=(const DInterval& s){
  return capd::vectalg::assignFromScalar(*this,s);
}

inline IVector& IVector::operator+=(const DInterval& s){
  return capd::vectalg::addAssignObjectScalar(*this,s);
}

inline IVector& IVector::operator-=(const DInterval& s){
  return capd::vectalg::subtractAssignObjectScalar(*this,s);
}

inline IVector& IVector::operator*=(const DInterval& s){
  return capd::vectalg::multiplyAssignObjectScalar(*this,s);
}

inline IVector& IVector::operator/=(const DInterval& s){
  return capd::vectalg::divideAssignObjectScalar(*this,s);
}

inline bool operator< (const IVector& v1, const IVector& v2){
  return capd::vectalg::lessThan(v1,v2);
}

inline bool operator> (const IVector& v1, const IVector& v2){
  return capd::vectalg::greaterThan(v1,v2);
}

inline bool operator<= (const IVector& v1, const IVector& v2){
  return capd::vectalg::lessEqual(v1,v2);
}


inline bool operator>= (const IVector& v1, const IVector& v2){
  return capd::vectalg::greaterEqual(v1,v2);
}

// ----------------------------------- equality --------------------------------------

inline bool operator== (const IVector& v1, const IVector& v2){
  return capd::vectalg::equal(v1,v2);
}


inline bool operator!= (const IVector& v1, const IVector& v2){
  return capd::vectalg::notEqual(v1,v2);
}

}} // the end of the namespace capd::facade

#endif // _CAPD_FACADE_IVECTOR_H_


