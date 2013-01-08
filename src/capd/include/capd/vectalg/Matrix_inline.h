/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Matrix_inline.h
///
/// @author The CAPD group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file is part of the CAPD library.  This library is free software;
// you can redistribute it and/or modify it under the terms of the GNU
// General Public License as published by the Free Software Foundation;
// either version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this software; see the file "license.txt".  If not, write to the
// Free Software Foundation, Inc., 59

#ifndef _CAPD_VECTALG_MATRIX_INLINE_H_ 
#define _CAPD_VECTALG_MATRIX_INLINE_H_ 

#include "capd/vectalg/Matrix.h"

namespace capd{
namespace vectalg{

template<typename Scalar, int rows, int cols>
inline void Matrix<Scalar,rows,cols>::clear(){
  capd::vectalg::clear(*this);
}

// --------------------- multiplication matrix*vector, matrix*matrix ----------------

template<typename Scalar,int rows,int cols>
inline Vector<Scalar,rows> operator*(const Matrix<Scalar,rows,cols>& m, const Vector<Scalar,cols>& v){
  return matrixByVector< Vector<Scalar,rows> > (m,v);
}

template<typename Scalar,int rows,int cols>
inline Vector<Scalar,rows> operator*(const Matrix<Scalar,rows,cols>& a, const ColumnVector<Scalar,cols>&v){
  return matrixByVector< Vector<Scalar,rows> > (a,v);
}

template<typename Scalar, int rows, int cols>
inline Vector<Scalar,rows> operator*(const Matrix<Scalar,rows,cols>& m, const RowVector<Scalar,cols>& u){
  return matrixByVector< Vector<Scalar,rows> >(m,u);
}

template<typename Scalar, int rows, int cols1, int cols2>
Matrix<Scalar,rows,cols2> operator*(const Matrix<Scalar,rows,cols1>& a1, const Matrix<Scalar,cols1,cols2>& a2){
  return matrixByMatrix< Matrix<Scalar,rows,cols2> > (a1,a2);
}

// ---------------------------- abs(matrix) -----------------------------------------

template<typename Scalar,int rows, int cols>
inline Matrix<Scalar,rows,cols> abs(const Matrix<Scalar,rows,cols>& m){
  return absoluteValue< Matrix<Scalar,rows,cols> > (m);
}

// ---------------------------- unary minus -----------------------------------------

template<typename Scalar,int rows, int cols>
inline Matrix<Scalar,rows,cols> operator-(const Matrix<Scalar,rows,cols>& m){
  return unaryMinus< Matrix<Scalar,rows,cols> > (m);
}

// ---------------------------- matrix + matrix -------------------------------------

template<typename Scalar,int rows, int cols>
inline Matrix<Scalar,rows,cols> operator+(const Matrix<Scalar,rows,cols>& m1, const Matrix<Scalar,rows,cols>& m2){
  return addObjects< Matrix<Scalar,rows,cols> > (m1,m2);
}

// ---------------------------- matrix - matrix -------------------------------------

template<typename Scalar,int rows, int cols>
inline Matrix<Scalar,rows,cols> operator-(const Matrix<Scalar,rows,cols>& m1, const Matrix<Scalar,rows,cols>& m2){
  return subtractObjects< Matrix<Scalar,rows,cols> > (m1,m2);
}

// ---------------------------- matrix *,/ scalar -------------------------------------

template<typename Scalar, int rows,int cols>
inline Matrix<Scalar,rows,cols> operator*(const Matrix<Scalar,rows,cols>& m, const Scalar& s){
  return multiplyObjectScalar< Matrix<Scalar,rows,cols> > (m,s);
}

template<typename Scalar, int rows,int cols>
inline Matrix<Scalar,rows,cols> operator*(const Scalar& s, const Matrix<Scalar,rows,cols>& m){
  return multiplyObjectScalar< Matrix<Scalar,rows,cols> > (m,s);
}

template<typename Scalar, int rows,int cols>
inline Matrix<Scalar,rows,cols> operator/(const Matrix<Scalar,rows,cols>& m, const Scalar& s){
  return divideObjectScalar< Matrix<Scalar,rows,cols> > (m,s);
}

// ---------------------------- matrix + scalar -------------------------------------

template<typename Scalar, int rows,int cols>
inline Matrix<Scalar,rows,cols> operator+(const Matrix<Scalar,rows,cols>& m, const Scalar& s){
  return addObjectScalar< Matrix<Scalar,rows,cols> > (m,s);
}

// ---------------------------- matrix - scalar -------------------------------------

template<typename Scalar, int rows,int cols>
inline Matrix<Scalar,rows,cols> operator-(const Matrix<Scalar,rows,cols>& m, const Scalar& s){
  return subtractObjectScalar< Matrix<Scalar,rows,cols> > (m,s);
}

// ------------------------- inequalities - true if hold true on each coord ---------

template<typename Scalar, int rows,int cols>
inline bool operator<(const Matrix<Scalar,rows,cols>& m1, const Matrix<Scalar,rows,cols>& m2){
  return lessThan(m1,m2);
}

template<typename Scalar, int rows,int cols>
inline bool operator>(const Matrix<Scalar,rows,cols>& m1, const Matrix<Scalar,rows,cols>& m2){
  return greaterThan(m1,m2);
}

template<typename Scalar, int rows,int cols>
inline bool operator<=(const Matrix<Scalar,rows,cols>& m1, const Matrix<Scalar,rows,cols>& m2){
  return lessEqual(m1,m2);
}

template<typename Scalar, int rows,int cols>
inline bool operator>=(const Matrix<Scalar,rows,cols>&m1, const Matrix<Scalar,rows,cols>&m2){
  return greaterEqual(m1,m2);
}

template<typename Scalar,int rows, int cols>
inline bool operator==(const Matrix<Scalar,rows,cols> &a1,const Matrix<Scalar,rows,cols> &a2){
  return equal(a1,a2);
}

template<typename Scalar,int rows, int cols>
inline bool operator!=(const Matrix<Scalar,rows,cols> &a1,const Matrix<Scalar,rows,cols> &a2){
  return notEqual(a1,a2);
}

// ------------------ constructors -------------------------------------------------

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>::Matrix() : ContainerType()
{}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>::Matrix(int A_rows,int A_cols) 
  : ContainerType(A_rows,A_cols)
{}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>::Matrix(int A_rows,int A_cols,bool) 
  : ContainerType(A_rows,A_cols,true)
{}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>::Matrix(const Matrix& a_m) 
  : ContainerType(a_m)
{}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>::Matrix(const Dimension& A_dim)
  : ContainerType(A_dim)
{}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>::Matrix(const Dimension& A_dim,bool)
  : ContainerType(A_dim, true)
{}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>& Matrix<Scalar,rows,cols>::operator=(const Matrix& a){
   ContainerType::operator=(a);
   return *this;
}

// ----------------------------- indexing ---------------------------------------------

template<typename Scalar, int rows, int cols>
inline RowVector<Scalar,cols> Matrix<Scalar,rows,cols>::operator[](int i) const {
   return RowVector<Scalar,cols>(data+i*numberOfColumns(),numberOfColumns());
}


template<typename Scalar, int rows, int cols>
inline RowVector<Scalar,cols> Matrix<Scalar,rows,cols>::operator()(int i) const{
   return RowVector<Scalar,cols>(data + --i*numberOfColumns(),numberOfColumns());
}

template<typename Scalar, int rows, int cols>
inline RowVector<Scalar,cols> Matrix<Scalar,rows,cols>::row(int i) const{
   return RowVector<Scalar,cols>(data+i*numberOfColumns(),numberOfColumns());
}

template<typename Scalar, int rows, int cols>
inline ColumnVector<Scalar,rows> Matrix<Scalar,rows,cols>::column(int i) const{
   return ColumnVector<Scalar,rows>(data+i,numberOfColumns(),numberOfRows());
}

template<typename Scalar, int rows, int cols>
inline Scalar& Matrix<Scalar,rows,cols>::operator()(int i,int j){
   return data[ --i*numberOfColumns() + --j];
}

template<typename Scalar, int rows, int cols>
inline const Scalar& Matrix<Scalar,rows,cols>::operator()(int i,int j) const{
   return data[ --i*numberOfColumns() + --j];
}

template<typename Scalar, int rows, int cols>
inline Scalar* Matrix<Scalar,rows,cols>::at(int i,int j){
   return data + --i*numberOfColumns() + --j;
}

template<typename Scalar, int rows, int cols>
inline const Scalar* Matrix<Scalar,rows,cols>::at(int i,int j) const{
   return data + --i*numberOfColumns() + --j;
}

// ------------------------ iterators ----------------------------- //

template<typename Scalar, int rows, int cols>
inline MatrixIterator< Matrix<Scalar,rows,cols> > 
Matrix<Scalar,rows,cols>::beginMatrix() {
  return MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(1,1));
}

template<typename Scalar, int rows, int cols>
inline MatrixIterator< Matrix<Scalar,rows,cols> > 
Matrix<Scalar,rows,cols>::endMatrix(){
  return MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(numberOfRows(),numberOfColumns()+1));
}

template<typename Scalar, int rows, int cols>
inline MatrixIterator< Matrix<Scalar,rows,cols> > Matrix<Scalar,rows,cols>::beginOfRow(int i){
  return MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(i,1));
}

template<typename Scalar, int rows, int cols>
inline MatrixIterator< Matrix<Scalar,rows,cols> > Matrix<Scalar,rows,cols>::beginOfColumn(int j){
  return MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(1,j));
}

template<typename Scalar, int rows, int cols>
inline MatrixIterator< Matrix<Scalar,rows,cols> > Matrix<Scalar,rows,cols>::endOfRow(int i){
  return MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(i,numberOfColumns()+1));
}

template<typename Scalar, int rows, int cols>
inline MatrixIterator< Matrix<Scalar,rows,cols> > Matrix<Scalar,rows,cols>::endOfColumn(int j){
  return MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(numberOfRows(),j+1));
}


template<typename Scalar, int rows, int cols>
inline const_MatrixIterator< Matrix<Scalar,rows,cols> > 
Matrix<Scalar,rows,cols>::beginMatrix() const{
  return const_MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(1,1));
}

template<typename Scalar, int rows, int cols>
inline const_MatrixIterator< Matrix<Scalar,rows,cols> > 
Matrix<Scalar,rows,cols>::endMatrix() const{
  return const_MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(numberOfRows(),numberOfColumns()+1));
}

template<typename Scalar, int rows, int cols>
inline const_MatrixIterator< Matrix<Scalar,rows,cols> > 
Matrix<Scalar,rows,cols>::beginOfRow(int i) const{
  return const_MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(i,1));
}

template<typename Scalar, int rows, int cols>
inline const_MatrixIterator< Matrix<Scalar,rows,cols> > 
Matrix<Scalar,rows,cols>::beginOfColumn(int j) const{
  return const_MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(1,j));
}

template<typename Scalar, int rows, int cols>
inline const_MatrixIterator< Matrix<Scalar,rows,cols> > 
Matrix<Scalar,rows,cols>::endOfRow(int i) const{
  return const_MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(i,numberOfColumns()+1));
}

template<typename Scalar, int rows, int cols>
inline const_MatrixIterator< Matrix<Scalar,rows,cols> > 
Matrix<Scalar,rows,cols>::endOfColumn(int j) const{
  return const_MatrixIterator< Matrix<Scalar,rows,cols> >(*this,at(numberOfRows(),j+1));
}

//------------------------ assignments - Scalars ------------------------//

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>& Matrix<Scalar,rows,cols>::operator=(const Scalar &s){
  return assignFromScalar(*this,s);
}


template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>& Matrix<Scalar,rows,cols>::operator+=(const Scalar &s){
  return addAssignObjectScalar(*this,s);
}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>& Matrix<Scalar,rows,cols>::operator-=(const Scalar &s){
  return subtractAssignObjectScalar(*this,s);
}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>& Matrix<Scalar,rows,cols>::operator*=(const Scalar &s){
  return multiplyAssignObjectScalar(*this,s);
}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>& Matrix<Scalar,rows,cols>::operator/=(const Scalar &s){
  return divideAssignObjectScalar(*this,s);
}

//------------------------- assignments - matrices --------------------//

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>& Matrix<Scalar,rows,cols>::operator+=(const Matrix& a){
  return addAssignObjectObject(*this,a);
}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,rows,cols>& Matrix<Scalar,rows,cols>::operator-=(const Matrix& a){
  return subtractAssignObjectObject(*this,a);
}


}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_MATRIX_INLINE_H_ 

/// @}
