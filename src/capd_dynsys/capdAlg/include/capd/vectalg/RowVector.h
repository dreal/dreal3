/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file RowVector.h
///
/// This file provides a template class RowVector
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_VECTALG_ROWVECTOR_H_ 
#define _CAPD_VECTALG_ROWVECTOR_H_ 

#include <ostream>
#include "capd/vectalg/Vector.h"

namespace capd{
namespace vectalg{

////////////////////////////////////////////////////////////////////////////
///
/// RowVector class realizes a vector without its own container.
/// He is just a reference to a part of other object (i.e. Matrix of Vector)
/// with his own container.
///
/// It is assumed that data fill continuous part of a memory
/// Compare with ColumnVector 
///
template<typename Scalar, int cols>
class RowVector
{
public:
  typedef Scalar ScalarType;
  typedef ScalarType* iterator;
  typedef const ScalarType* const_iterator;
  typedef RowVector<Scalar,cols> VectorType;
  typedef RowVector ContainerType;
  
  RowVector(const Scalar* a_pointer, int a_dim);
  
  RowVector& operator=(const RowVector&);
  RowVector& operator=(const Vector<Scalar,cols>&);
  RowVector& operator+=(const RowVector&);
  RowVector& operator+=(const Vector<Scalar,cols>&);
  RowVector& operator-=(const RowVector&);
  RowVector& operator-=(const Vector<Scalar,cols>&);
  RowVector& operator*=(const Scalar&);
  RowVector& operator/=(const Scalar&);
  operator Vector<Scalar,cols>() const;
  
  inline Scalar& operator[](int a_col);
  inline const Scalar& operator[](int a_col) const;
  
  Scalar euclNorm() const;
  bool normalize();
  void clear();
  int dimension() const;
  
  iterator begin();
  iterator end();
  const_iterator begin() const;
  const_iterator end() const;
  void assertEqualSize(const RowVector& c) const;

  template<typename U>
  struct rebind {
      typedef RowVector<U,cols> other;
  };

protected:
  Scalar* m_pointer;
  int m_dim;
}; // class RowVector

template<typename Scalar, int cols>
Vector<Scalar, cols> diam(const RowVector<Scalar, cols> & v);

// -------------------------- inline definitions ------------------------

template<typename Scalar, int cols>
inline RowVector<Scalar,cols>::RowVector(const Scalar* a_pointer, int a_dim)
    : m_pointer(const_cast<Scalar*>(a_pointer)),
      m_dim(a_dim)
{}

template<typename Scalar, int cols>
inline Scalar& RowVector<Scalar,cols>::operator[](int a_col){
  return *(m_pointer+a_col);
}

template<typename Scalar, int cols>
inline const Scalar& RowVector<Scalar,cols>::operator[](int a_col) const{
  return *(m_pointer+a_col);
}

template<typename Scalar, int cols>
inline int RowVector<Scalar,cols>::dimension() const{
  return m_dim;
}

// ------------------------ iterator selection --------------------------

template<typename Scalar, int cols>
inline typename RowVector<Scalar,cols>::iterator RowVector<Scalar,cols>::begin(){
  return iterator(m_pointer);
}

template<typename Scalar, int cols>
inline typename RowVector<Scalar,cols>::iterator RowVector<Scalar,cols>::end(){
  return iterator(m_pointer+m_dim);
}

template<typename Scalar, int cols>
inline typename RowVector<Scalar,cols>::const_iterator 
RowVector<Scalar,cols>::begin() const{
  return const_iterator(m_pointer);
}

template<typename Scalar, int cols>
inline typename RowVector<Scalar,cols>::const_iterator 
RowVector<Scalar,cols>::end() const{
  return const_iterator(m_pointer+m_dim);
}

template<typename Scalar, int cols>
inline void RowVector<Scalar,cols>::assertEqualSize(const RowVector& c) const{
  if(m_dim!=c.dimension())
    throw std::runtime_error("Unequal dimensions in RowVector::assertEqualDimension");
}

// ---------------------------- operator + -------------------------------------------

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator+(const Vector<Scalar,cols>& u1, const RowVector<Scalar,cols>& u2){
  return addObjects< Vector<Scalar,cols> > (u1,u2);
}

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator+(const RowVector<Scalar,cols>&u1, const Vector<Scalar,cols>&u2){
  return addObjects< Vector<Scalar,cols> > (u1,u2);
}

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator+(const RowVector<Scalar,cols>&u1, const RowVector<Scalar,cols>&u2){
  return addObjects< Vector<Scalar,cols> > (u1,u2);
}

// ---------------------------- operator - -------------------------------------------

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator-(const Vector<Scalar,cols>& u1, const RowVector<Scalar,cols>& u2){
  return subtractObjects< Vector<Scalar,cols> > (u1,u2);
}

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator-(const RowVector<Scalar,cols>&u1, const Vector<Scalar,cols>&u2){
  return subtractObjects< Vector<Scalar,cols> > (u1,u2);
}

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator-(const RowVector<Scalar,cols>&u1, const RowVector<Scalar,cols>&u2){
  return subtractObjects< Vector<Scalar,cols> > (u1,u2);
}

// ---------------------------- scalar product -------------------------------------------

template<typename Scalar, int cols>
inline Scalar operator*(const Vector<Scalar,cols>&u1, const RowVector<Scalar,cols>&u2){
  return scalarProduct(u1,u2);
}

template<typename Scalar, int cols>
inline Scalar operator*(const RowVector<Scalar,cols>&u1, const Vector<Scalar,cols>&u2){
  return scalarProduct(u1,u2);
}

template<typename Scalar, int cols>
inline Scalar operator*(const RowVector<Scalar,cols>&u1, const RowVector<Scalar,cols>&u2){
  return scalarProduct(u1,u2);
}


// ------------------------------- unary minus ------------------------------------------

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator-(const RowVector<Scalar,cols>& u){
  return unaryMinus < Vector<Scalar,cols> > (u);
}

// ------------------------------ multiplication and division by scalar -----------------

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator*(const Scalar& s, const RowVector<Scalar,cols>& u){
  return multiplyObjectScalar< Vector<Scalar,cols> > (u,s);
}

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator*(const RowVector<Scalar,cols>& u, const Scalar& s){
  return multiplyObjectScalar< Vector<Scalar,cols> > (u,s);
}

template<typename Scalar, int cols>
inline Vector<Scalar,cols> operator/(const RowVector<Scalar,cols>& u, const Scalar& s){
  return divideObjectScalar< Vector<Scalar,cols> > (u,s);
}

template<typename Scalar, int cols>
inline RowVector<Scalar,cols>& RowVector<Scalar,cols>::operator/=(const Scalar& s){
  return divideAssignObjectScalar(*this,s);
}

template<typename Scalar, int cols>
inline RowVector<Scalar,cols>& RowVector<Scalar,cols>::operator*=(const Scalar& s){
  return multiplyAssignObjectScalar(*this,s);
}


// ------------------------- output -----------------------------------------------------

template<typename Scalar, int cols>
inline std::ostream& operator << (std::ostream& out, const RowVector<Scalar,cols>& u){
  return out << Vector<Scalar,cols>(u);
}

// -------------------------- norm and normalization -----------------------------------

template<typename Scalar,int cols>
inline Scalar RowVector<Scalar,cols>::euclNorm() const{
  return capd::vectalg::euclNorm(*this);
}

template<typename Scalar, int cols>
inline bool RowVector<Scalar,cols>::normalize(){
  return capd::vectalg::normalize(*this);
}

// ------------------------------- clear --------------------------------------------

template<typename Scalar,int cols>
inline void RowVector<Scalar,cols>::clear(){
  capd::vectalg::clear(*this);
}

// ------------------------------ assignment ----------------------------------------

template<typename Scalar,int cols>
inline RowVector<Scalar,cols>& RowVector<Scalar,cols>::operator=(const RowVector& v){
  return assignObjectObject(*this,v);
}

template<typename Scalar,int cols>
inline RowVector<Scalar,cols>& RowVector<Scalar,cols>::operator=(const Vector<Scalar,cols>& v){
  return assignObjectObject(*this,v);
}


template<typename Scalar,int cols>
inline RowVector<Scalar,cols>& RowVector<Scalar,cols>::operator+=(const RowVector& v){
  return addAssignObjectObject(*this,v);
}

template<typename Scalar,int cols>
inline RowVector<Scalar,cols>& RowVector<Scalar,cols>::operator+=(const Vector<Scalar,cols>& v){
  return addAssignObjectObject(*this,v);
}

template<typename Scalar,int cols>
inline RowVector<Scalar,cols>& RowVector<Scalar,cols>::operator-=(const RowVector& v){
  return subtractAssignObjectObject(*this,v);
}

template<typename Scalar,int cols>
inline RowVector<Scalar,cols>& RowVector<Scalar,cols>::operator-=(const Vector<Scalar,cols>& v){
  return subtractAssignObjectObject(*this,v);
}

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_ROWVECTOR_H_ 

/// @}
