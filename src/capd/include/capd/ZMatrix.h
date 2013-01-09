/// @addtogroup facade
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ZMatrix.h
///
/// This file provides a class ZMatrix which is a facade of template
/// class Matrix. The class realizes matrices of variable dimensions
/// with integer coordinates
///
/// The main intention of providing this code is to make simpler usage of
/// template classes
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

 

#ifndef _CAPD_ZMATRIX_H_
#define _CAPD_ZMATRIX_H_

#include <iostream>

#include "capd/ZVector.h"
#include "capd/vectalg/Matrix.h"

namespace capd{

class ZMatrix
{
public:
  typedef int ScalarType;
  typedef capd::vectalg::Matrix<int,0,0> BaseMatrix;
  typedef ZMatrix MatrixType;
  typedef BaseMatrix::ContainerType ContainerType;
  typedef ContainerType::iterator iterator;
  typedef ContainerType::const_iterator const_iterator;
  typedef ContainerType::Dimension Dimension;
  
  typedef DVector RowVectorType;
  typedef DVector ColumnVectorType;
  typedef capd::vectalg::RowVector<int,0> RefRowVectorType;
  typedef capd::vectalg::ColumnVector<int,0> RefColumnVectorType;

  //constructors
  ZMatrix(){}
  ZMatrix(int rows,int cols) 
    : m_M(rows,cols) 
  {}
  
  ZMatrix(int rows,int cols, const ScalarType data[])
    : m_M(rows,cols,data)
  {}
  
  ZMatrix(const ZMatrix& m)
    : m_M(m.m_M)
  {}
  
  ZMatrix(const Dimension& dim)
    : m_M(dim)
  {}

  ZMatrix(const Dimension& d,bool b)
    : m_M(d,b)
  {}

  ZMatrix(int rows,int cols,bool b)
    : m_M(rows,cols,b)
  {}
  
  void clear(){
    m_M.clear();
  }
  
  //assignments - matrices
  ZMatrix& operator= (const ZMatrix& a);         //assign a matrix
  ZMatrix& operator+=(const ZMatrix& a);         //increase by a matrix
  ZMatrix& operator-=(const ZMatrix& a);         //decrease by a matrix
  
  //assignments - Scalars
  ZMatrix& operator= (const int s);         //assign a int
  ZMatrix& operator+=(const int s);         //increase by a int
  ZMatrix& operator-=(const int s);         //decrease by a int
  ZMatrix& operator*=(const int s);         //rescale by multiplying
  ZMatrix& operator/=(const int s);         //rescale by dividing
  
  // iterator selections
  MatrixIterator< BaseMatrix > beginMatrix(){
    return m_M.beginMatrix();
  }
  MatrixIterator< BaseMatrix> endMatrix(){
    return m_M.endMatrix();
  }
  MatrixIterator< BaseMatrix > beginOfRow(int i){
    return m_M.beginOfRow(i);
  }
  MatrixIterator< BaseMatrix > beginOfColumn(int j){
    return m_M.beginOfColumn(j);
  }
  MatrixIterator< BaseMatrix > endOfRow(int i){
    return m_M.endOfRow(i);
  }
  MatrixIterator< BaseMatrix > endOfColumn(int j){
    return m_M.endOfColumn(j);
  }
  
  const_MatrixIterator< BaseMatrix > beginMatrix() const{
    return m_M.beginMatrix();
  }
  const_MatrixIterator< BaseMatrix > endMatrix() const{
    return m_M.endMatrix();
  }
  const_MatrixIterator< BaseMatrix > beginOfRow(int i) const{
    return m_M.beginOfRow(i);
  }
  const_MatrixIterator< BaseMatrix > beginOfColumn(int j) const{
    return m_M.beginOfColumn(j);
  }
  const_MatrixIterator< BaseMatrix > endOfRow(int i) const{
    return m_M.endOfRow(i);
  }
  const_MatrixIterator< BaseMatrix > endOfColumn(int j) const{
    return m_M.endOfColumn(j);
  }

  iterator begin(){
    return m_M.begin();
  }
  iterator end(){
    return m_M.end();
  }
  const_iterator begin() const{
    return m_M.begin();
  }
  const_iterator end() const{
    return m_M.end();
  }

  //indexing
  RefRowVectorType operator[](int i) const{
    return m_M[i];
  }
  RefRowVectorType operator()(int i) const{
    return m_M[i];
  }
  int& operator()(int i,int j){
    return m_M(i,j);
  }
  const int& operator()(int i,int j) const{
    return m_M(i,j);
  }
  int* at(int i,int j){
    return m_M.at(i,j);
  }
  const int* at(int i,int j) const{
    return m_M.at(i,j);
  }

  //operations on matrices
  static ZMatrix Identity(int dimension){
    ZMatrix r(dimension,dimension,true);
    r.setToIdentity();
    return r;
  }
  void setToIdentity(){
    m_M.setToIdentity();
  }
  RefRowVectorType row(int i) const{
    return m_M.row(i);
  }
  RefColumnVectorType column(int j) const{
    return m_M.column(j);
  }
  void Transpose(){
    m_M.Transpose();
  }

  int rowStride()const {
    return m_M.numberOfColumns();
  } // difference of pointers when moving to the next row in the same column
  int columnStride()const{
    return 1;
  }  // difference of pointers when moving to the next column in the same row

  Dimension dimension() const{
    return m_M.dimension();
  }
  int size() const{
    return m_M.size();
  }
  int numberOfRows() const{
    return m_M.numberOfRows();
  }
  int numberOfColumns() const{
    return m_M.numberOfColumns();
  }

  void* operator new[](size_t sizeOfData){
    return ::operator new[](sizeOfData);
  }

  void* operator new[](size_t sizeOfData,int rows, int cols)
  {
    BaseMatrix::setDefaultDimension(std::pair<int,int>(rows,cols));
    return ::operator new[](sizeOfData);
  }

  BaseMatrix m_M;
}; //the end of class ZMatrix


inline ZMatrix operator*(const ZMatrix& m1, const ZMatrix& m2){
  return capd::vectalg::matrixByMatrix<ZMatrix>(m1,m2);
}

inline ZMatrix Transpose(const ZMatrix& m1){
  ZMatrix result(m1);
  result.Transpose();
  return result;
}

inline std::ostream &operator<<(std::ostream& out, const ZMatrix& m){
  return out << m.m_M;
}

inline std::istream &operator>>(std::istream& inp, ZMatrix& m){
  return inp >> m;
}


// ########################################################################### //

// --------------------- multiplication matrix*vector, matrix*matrix ----------------

inline DVector operator*(const ZMatrix& m, const DVector& v){
  return capd::vectalg::matrixByVector<DVector> (m,v);
}

inline DVector operator*(const ZMatrix& a, const ZMatrix::RefColumnVectorType&v){
  return capd::vectalg::matrixByVector<DVector> (a,v);
}

inline DVector operator*(const ZMatrix& m, const ZMatrix::RefRowVectorType& u){
  return capd::vectalg::matrixByVector<DVector> (m,u);
}

// ---------------------------- abs(matrix) -----------------------------------------

inline ZMatrix abs(const ZMatrix& m){
  return capd::vectalg::absoluteValue<ZMatrix> (m);
}

// ---------------------------- unary minus -----------------------------------------

inline ZMatrix operator-(const ZMatrix& m){
  return capd::vectalg::unaryMinus<ZMatrix> (m);
}

// ---------------------------- matrix + matrix -------------------------------------

inline ZMatrix operator+(const ZMatrix& m1, const ZMatrix& m2){
  return capd::vectalg::addObjects<ZMatrix> (m1,m2);
}

// ---------------------------- matrix - matrix -------------------------------------

inline ZMatrix operator-(const ZMatrix& m1, const ZMatrix& m2){
  return capd::vectalg::subtractObjects<ZMatrix> (m1,m2);
}

// ---------------------------- matrix *,/ scalar -------------------------------------

inline ZMatrix operator*(const ZMatrix& m, const int s){
  return capd::vectalg::multiplyObjectScalar<ZMatrix> (m,s);
}

inline ZMatrix operator*(const int s, const ZMatrix& m){
  return capd::vectalg::multiplyObjectScalar<ZMatrix> (m,s);
}

inline ZMatrix operator/(const ZMatrix& m, const int s){
  return capd::vectalg::divideObjectScalar<ZMatrix> (m,s);
}

// ---------------------------- matrix + scalar -------------------------------------

inline ZMatrix operator+(const ZMatrix& m, const int s){
  return capd::vectalg::addObjectScalar<ZMatrix> (m,s);
}

// ---------------------------- matrix - scalar -------------------------------------

inline ZMatrix operator-(const ZMatrix& m, const int s){
  return capd::vectalg::subtractObjectScalar<ZMatrix> (m,s);
}

// ------------------------- inequalities - true if hold true on each coord ---------

inline bool operator<(const ZMatrix& m1, const ZMatrix& m2){
  return capd::vectalg::lessThan(m1,m2);
}

inline bool operator>(const ZMatrix& m1, const ZMatrix& m2){
  return capd::vectalg::greaterThan(m1,m2);
}

inline bool operator<=(const ZMatrix& m1, const ZMatrix& m2){
  return capd::vectalg::lessEqual(m1,m2);
}

inline bool operator>=(const ZMatrix&m1, const ZMatrix&m2){
  return capd::vectalg::greaterEqual(m1,m2);
}

inline bool operator==(const ZMatrix &a1,const ZMatrix &a2){
  return capd::vectalg::equal(a1,a2);
}

inline bool operator!=(const ZMatrix &a1,const ZMatrix &a2){
  return capd::vectalg::notEqual(a1,a2);
}

//------------------------ assignments - Scalars ------------------------//

inline ZMatrix& ZMatrix::operator=(const int s){
  return capd::vectalg::assignFromScalar(*this,s);
}

inline ZMatrix& ZMatrix::operator+=(const int s){
  return capd::vectalg::addAssignObjectScalar(*this,s);
}

inline ZMatrix& ZMatrix::operator-=(const int s){
  return capd::vectalg::subtractAssignObjectScalar(*this,s);
}

inline ZMatrix& ZMatrix::operator*=(const int s){
  return capd::vectalg::multiplyAssignObjectScalar(*this,s);
}

inline ZMatrix& ZMatrix::operator/=(const int s){
  return capd::vectalg::divideAssignObjectScalar(*this,s);
}

//------------------------- assignments - matrices --------------------//

inline ZMatrix& ZMatrix::operator+=(const ZMatrix& a){
  return capd::vectalg::addAssignObjectObject(*this,a);
}

inline ZMatrix& ZMatrix::operator-=(const ZMatrix& a){
  return capd::vectalg::subtractAssignObjectObject(*this,a);
}

} // namespace capd

#endif // _CAPD_IMATRIX_H_

/// @}
