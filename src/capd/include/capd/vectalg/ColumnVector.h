/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ColumnVector.h
///
/// This file provides a template class ColumnVector
/// This class realizes a vector without own container, which is a reference 
/// to a subset of other object with his own container.
/// A typical situation is a column of matrix which can be consider as a vector
///
/// The file 'RowVector.h' defines similar class, but in that case it is assumed
/// that data fill continuous part of a memory 
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_VECTALG_COLUMNVECTOR_H_ 
#define _CAPD_VECTALG_COLUMNVECTOR_H_ 

#include <ostream>
#include "capd/vectalg/Vector.h"

namespace capd{
namespace vectalg{

template<typename Scalar>
class ColumnIterator{
public:
  typedef Scalar ScalarType;

  inline ColumnIterator(ScalarType *a_p, int a_pointerStride)
  : m_Pointer(a_p), m_pointerStride(a_pointerStride)
  {}

  inline ColumnIterator operator++(int)
  {
    ColumnIterator it(*this);
    m_Pointer += m_pointerStride;
    return it;
  }

  inline ColumnIterator operator--(int)
  {
    ColumnIterator it(*this);
    m_Pointer -= m_pointerStride;
    return it;
  }

  inline ColumnIterator& operator++()
  {
    m_Pointer += m_pointerStride;
    return *this;
  }

  inline ColumnIterator& operator--()
  {
    m_Pointer -= m_pointerStride;
    return *this;
  }

  inline ColumnIterator& operator+=(int jump)
  {
    m_Pointer+= jump*m_pointerStride;
    return *this;
  }

  inline ColumnIterator& operator-=(int jump)
  {
    m_Pointer-= jump*m_pointerStride;
    return *this;
  }

  inline bool operator!=(const ColumnIterator& second)
  {
    return m_Pointer!=second.m_Pointer;
  }

  inline ScalarType& operator*()
  {
    return *m_Pointer;
  }

  inline ScalarType* operator->()
  {
    return m_Pointer;
  }

private:
  ScalarType *m_Pointer;
  int m_pointerStride;
  ColumnIterator(){} // we do not need a default constructor
};

// --------------------- const_iterator -------------------

template<typename Scalar>
class const_ColumnIterator{
public:
  typedef Scalar ScalarType;

  inline const_ColumnIterator(const ScalarType* a_p, int a_pointerStride)
    : m_Pointer(a_p), m_pointerStride(a_pointerStride)
  {}

  inline const_ColumnIterator operator++(int)
  {
    const_ColumnIterator it(*this);
    m_Pointer += m_pointerStride;
    return it;
  }

  inline const_ColumnIterator operator--(int)
  {
    const_ColumnIterator it(*this);
    m_Pointer -= m_pointerStride;
    return it;
  }

  inline const_ColumnIterator& operator++()
  {
    m_Pointer += m_pointerStride;
    return *this;
  }

  inline const_ColumnIterator& operator--()
  {
    m_Pointer -= m_pointerStride;
    return *this;
  }

  inline const_ColumnIterator& operator+=(int jump)
  {
    m_Pointer += jump*m_pointerStride;
    return *this;
  }

  inline const_ColumnIterator& operator-=(int jump)
  {
    m_Pointer -= jump*m_pointerStride;
    return *this;
  }

  inline bool operator!=(const const_ColumnIterator& second)
  {
    return m_Pointer!=second.m_Pointer;
  }

  inline const ScalarType& operator*()
  {
    return *m_Pointer;
  }

  inline const ScalarType* operator->()
  {
    return m_Pointer;
  }
private:
  const ScalarType*  m_Pointer;
  const_ColumnIterator(){} // we do not need a default constructor
  int m_pointerStride;
};


template<typename Scalar, int rows, int cols>
class Matrix;

template<typename Scalar,int dim>
class Vector;

/// This class realizes a vector without its own container, which is a reference 
/// to a subset of other object with his own container.
/// A typical situation is a column of matrix which can be considered as a vector
///
template<typename Scalar, int rows>
class ColumnVector
{
public:
  typedef Scalar ScalarType;
  typedef capd::vectalg::ColumnIterator<Scalar> iterator;
  typedef capd::vectalg::const_ColumnIterator<Scalar> const_iterator;
  typedef ColumnVector VectorType;
  typedef ColumnVector ContainerType;

  ColumnVector(const Scalar* a_pointer, int a_stride, int a_dim);
  ColumnVector& operator=(const ColumnVector&);
  ColumnVector& operator=(const Vector<Scalar,rows>&);
  ColumnVector& operator+=(const ColumnVector&);
  ColumnVector& operator+=(const Vector<Scalar,rows>&);
  ColumnVector& operator-=(const ColumnVector&);
  ColumnVector& operator-=(const Vector<Scalar,rows>&);
  ColumnVector& operator*=(const Scalar&);
  ColumnVector& operator/=(const Scalar&);
  operator Vector<Scalar,rows>() const;

  Scalar& operator[](int a_row);
  const Scalar& operator[](int a_row) const;

  Scalar euclNorm() const;
  bool normalize();
  void clear();
  int dimension() const;

  iterator begin();
  iterator end();
  const_iterator begin() const;
  const_iterator end() const;
   
  void assertEqualSize(const ColumnVector& c) const;
protected:
  Scalar* m_pointer;
  int m_stride, m_dim;
}; // end of class ColumnVector

// -------------------------- inline definitions ------------------------

template<typename Scalar, int rows>
inline std::ostream& operator << (std::ostream& out, const ColumnVector<Scalar,rows>& s){
  return out << Vector<Scalar,rows>(s);
}

template<typename Scalar,int rows>
inline Scalar ColumnVector<Scalar,rows>::euclNorm() const{
  return capd::vectalg::euclNorm(*this);
}

template<typename Scalar,int rows>
inline bool ColumnVector<Scalar,rows>::normalize(){
  return capd::vectalg::normalize(*this);
}

template<typename Scalar,int rows>
inline ColumnVector<Scalar,rows>& ColumnVector<Scalar,rows>::operator=(const ColumnVector& v){
  return assignObjectObject(*this,v);
}

template<typename Scalar,int rows>
inline ColumnVector<Scalar,rows>& ColumnVector<Scalar,rows>::operator=(const Vector<Scalar,rows>& v){
  return assignObjectObject(*this,v);
}

// ----------------------- iterator selection ---------------------------

template<typename Scalar, int rows>
inline int ColumnVector<Scalar,rows>::dimension() const{
  return m_dim;
}

template<typename Scalar, int rows>
inline typename ColumnVector<Scalar,rows>::iterator 
ColumnVector<Scalar,rows>::begin(){
  return iterator(m_pointer,m_stride);
}

template<typename Scalar, int rows>
inline typename ColumnVector<Scalar,rows>::iterator 
ColumnVector<Scalar,rows>::end(){
  return iterator(m_pointer+m_dim*m_stride, m_stride);
}

template<typename Scalar, int rows>
inline typename ColumnVector<Scalar,rows>::const_iterator 
ColumnVector<Scalar,rows>::begin() const{
  return const_iterator(m_pointer, m_stride);
}

template<typename Scalar, int rows>
inline typename ColumnVector<Scalar,rows>::const_iterator 
ColumnVector<Scalar,rows>::end() const{
  return const_iterator(m_pointer+m_dim*m_stride, m_stride);
}

// ------------------------------ resize -----------------------------------

template<typename Scalar, int rows>
inline void ColumnVector<Scalar,rows>::assertEqualSize(const ColumnVector& c) const{
  if(m_dim!=c.dimension())
    throw std::runtime_error("Unequal dimensions in ColumnVector::assertEqualSize");
}

// ------------------------------ constructor -----------------------------

template<typename Scalar, int rows>
inline ColumnVector<Scalar,rows>::ColumnVector(const Scalar* a_pointer, int a_stride, int a_dim)
    : m_pointer(const_cast<Scalar*>(a_pointer)),
      m_stride(a_stride), m_dim(a_dim)
{}

template<typename Scalar, int rows>
inline Scalar& ColumnVector<Scalar,rows>::operator[](int a_row){
  return *(m_pointer + a_row*m_stride);
}

template<typename Scalar, int rows>
inline const Scalar& ColumnVector<Scalar,rows>::operator[](int a_row) const{
  return *(m_pointer + a_row*m_stride);
}

// -------------------- operator + ------------------------------------------

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator+(const Vector<Scalar,rows>& u, 
                                       const ColumnVector<Scalar,rows>& v
                                      )
{
  return addObjects< Vector<Scalar,rows>, Vector<Scalar,rows>, ColumnVector<Scalar,rows> > (u,v);
}

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator+(const ColumnVector<Scalar,rows>&v, 
                                       const Vector<Scalar,rows>&u
                                      )
{
  return addObjects< Vector<Scalar,rows>, Vector<Scalar,rows>, ColumnVector<Scalar,rows> > (u,v);
}

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator+(const ColumnVector<Scalar,rows>&u, 
                                       const ColumnVector<Scalar,rows>&v
                                      )
{
  return addObjects< Vector<Scalar,rows>, ColumnVector<Scalar,rows>, ColumnVector<Scalar,rows> > (u,v);
}

// -------------------- operator - ------------------------------------------

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator-(const Vector<Scalar,rows>& u, 
                                       const ColumnVector<Scalar,rows>& v
                                      )
{
  return subtractObjects< Vector<Scalar,rows>, Vector<Scalar,rows>, ColumnVector<Scalar,rows> > (u,v);
}

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator-(const ColumnVector<Scalar,rows>&v, 
                                       const Vector<Scalar,rows>&u
                                      )
{
  return subtractObjects< Vector<Scalar,rows>, Vector<Scalar,rows>, ColumnVector<Scalar,rows> > (u,v);
}

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator-(const ColumnVector<Scalar,rows>&u, 
                                       const ColumnVector<Scalar,rows>&v
                                      )
{
  return subtractObjects< Vector<Scalar,rows>, ColumnVector<Scalar,rows>, ColumnVector<Scalar,rows> > (u,v);
}

// ------------------------------- scalar product ----------------------------

template<typename Scalar, int rows>
inline Scalar operator*(const Vector<Scalar,rows>& u, const ColumnVector<Scalar,rows>& v){
  return scalarProduct(u,v);
}

template<typename Scalar, int rows>
inline Scalar operator*(const ColumnVector<Scalar,rows>&v, const Vector<Scalar,rows>&u){
  return scalarProduct(u,v);
}

template<typename Scalar, int rows>
inline Scalar operator*(const ColumnVector<Scalar,rows>&v, const ColumnVector<Scalar,rows>&u){
  return scalarProduct(u,v);
}

// ------------------------- unary minus ----------------------------------------

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator-(const ColumnVector<Scalar,rows>&u){
  return unaryMinus< Vector<Scalar,rows>, ColumnVector<Scalar,rows> >(u);
}

// -------------------------- multiplication and division by scalar -------------

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator*(const Scalar&s, const ColumnVector<Scalar,rows>&u){
  return multiplyObjectScalar< Vector<Scalar,rows> > (u,s);
}

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator*(const ColumnVector<Scalar,rows>&u, const Scalar&s){
  return multiplyObjectScalar< Vector<Scalar,rows> > (u,s);
}

template<typename Scalar, int rows>
inline Vector<Scalar,rows> operator/(const ColumnVector<Scalar,rows>&u, const Scalar&s){
  return divideObjectScalar< Vector<Scalar,rows> > (u,s);
}

template<typename Scalar,int rows>
inline ColumnVector<Scalar,rows>& ColumnVector<Scalar,rows>::operator*=(const Scalar& s){
  return multiplyAssignObjectScalar(*this,s);
}

template<typename Scalar,int rows>
ColumnVector<Scalar,rows>& ColumnVector<Scalar,rows>::operator/=(const Scalar& s){
  return divideAssignObjectScalar(*this,s);
}

// -------------------------------------- assignments --------------------------------------- 

template<typename Scalar,int rows>
inline ColumnVector<Scalar,rows>& ColumnVector<Scalar,rows>::operator+=(const ColumnVector& v){
  return addAssignObjectObject(*this,v);
}

template<typename Scalar,int rows>
inline ColumnVector<Scalar,rows>& ColumnVector<Scalar,rows>::operator+=(const Vector<Scalar,rows>& v){
  return addAssignObjectObject(*this,v);
}

template<typename Scalar,int rows>
inline ColumnVector<Scalar,rows>& ColumnVector<Scalar,rows>::operator-=(const ColumnVector& v){
  return subtractAssignObjectObject(*this,v);
}

template<typename Scalar,int rows>
inline ColumnVector<Scalar,rows>& ColumnVector<Scalar,rows>::operator-=(const Vector<Scalar,rows>& v){
  return subtractAssignObjectObject(*this,v);
}


template<typename Scalar,int rows>
void ColumnVector<Scalar,rows>::clear(){
  capd::vectalg::clear(*this);
}

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_COLUMNVECTOR_H_ 

/// @}
