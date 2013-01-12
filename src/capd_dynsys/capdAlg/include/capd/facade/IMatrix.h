/////////////////////////////////////////////////////////////////////////////
/// @file IMatrix.h
///
/// This file provides a class IMatrix which is a facade of template
/// class Matrix. The class realizes matrices of variable dimensions
/// with interval coordinates
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



#ifndef _CAPD_FACADE_IMATRIX_H_
#define _CAPD_FACADE_IMATRIX_H_

#include <iostream>

#include "capd/facade/IVector.h"
#include "capd/vectalg/Matrix.h"
#include "capd/facade/DMatrix.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.h"

namespace capd{
namespace facade{

class IMatrix
{
public:
  typedef DInterval ScalarType;
  typedef capd::vectalg::Matrix<DInterval,0,0> BaseMatrix;
  typedef IMatrix MatrixType;
  typedef BaseMatrix::ContainerType ContainerType;
  typedef ContainerType::iterator iterator;
  typedef ContainerType::const_iterator const_iterator;
  typedef ContainerType::Dimension Dimension;

  typedef IVector RowVectorType;
  typedef IVector ColumnVectorType;
  typedef capd::vectalg::RowVector<DInterval,0> RefRowVectorType;
  typedef capd::vectalg::ColumnVector<DInterval,0> RefColumnVectorType;

  template<class U>
  struct rebind
  {
    typedef DMatrix other;
  };

  //constructors
  IMatrix(){}
  IMatrix(int rows,int cols)
    : m_M(rows,cols)
  {}

  IMatrix(int rows,int cols, const ScalarType data[])
    : m_M(rows,cols,data)
  {}

  IMatrix(const IMatrix& m)
    : m_M(m.m_M)
  {}

  IMatrix(const Dimension& dim)
    : m_M(dim)
  {}

  IMatrix(const Dimension& d,bool b)
    : m_M(d,b)
  {}

  IMatrix(int rows,int cols,bool b)
    : m_M(rows,cols,b)
  {}

  void clear(){
    m_M.clear();
  }

  //assignments - matrices
  IMatrix& operator= (const IMatrix& a){
    m_M = a.m_M;
    return *this;
  }
  IMatrix& operator+=(const IMatrix& a);         //increase by a matrix
  IMatrix& operator-=(const IMatrix& a);         //decrease by a matrix

  //assignments - Scalars
  IMatrix& operator= (const DInterval& s);         //assign a DInterval
  IMatrix& operator+=(const DInterval& s);         //increase by a DInterval
  IMatrix& operator-=(const DInterval& s);         //decrease by a DInterval
  IMatrix& operator*=(const DInterval& s);         //rescale by multiplying
  IMatrix& operator/=(const DInterval& s);         //rescale by dividing

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
    return m_M(i);
  }
  DInterval& operator()(int i,int j){
    return m_M(i,j);
  }
  const DInterval& operator()(int i,int j) const{
    return m_M(i,j);
  }
  DInterval* at(int i,int j){
    return m_M.at(i,j);
  }
  const DInterval* at(int i,int j) const{
    return m_M.at(i,j);
  }

  //operations on matrices
  static IMatrix Identity(int dimension){
    IMatrix r(dimension,dimension,true);
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
}; //the end of class IMatrix


inline IMatrix operator*(const IMatrix& m1, const IMatrix& m2){
  return capd::vectalg::matrixByMatrix<IMatrix>(m1,m2);
}

inline IMatrix Transpose(const IMatrix& m1){
  IMatrix result(m1);
  result.Transpose();
  return result;
}

inline std::ostream &operator<<(std::ostream& out, const IMatrix& m){
  return out << m.m_M;
}

inline std::istream &operator>>(std::istream& inp, IMatrix& m){
  return inp >> m;
}


inline IMatrix midMatrix(const IMatrix& v){
  IMatrix result(v.dimension(),true);
  capd::vectalg::mid(v,result);
  return result;
}

inline void mid(const IMatrix& v, IMatrix&r){
  capd::vectalg::mid(v,r);
}

inline void split(IMatrix& u, IMatrix& v){
  capd::vectalg::split(u,v);
}

// ########################################################################### //

// --------------------- multiplication matrix*vector, matrix*matrix ----------------

inline IVector operator*(const IMatrix& m, const IVector& v){
  return capd::vectalg::matrixByVector<IVector> (m,v);
}

inline IVector operator*(const IMatrix& a, const IMatrix::RefColumnVectorType&v){
  return capd::vectalg::matrixByVector<IVector> (a,v);
}

inline IVector operator*(const IMatrix& m, const IMatrix::RefRowVectorType& u){
  return capd::vectalg::matrixByVector<IVector> (m,u);
}

// ---------------------------- abs(matrix) -----------------------------------------

inline IMatrix abs(const IMatrix& m){
  return capd::vectalg::absoluteValue<IMatrix> (m);
}

// ---------------------------- unary minus -----------------------------------------

inline IMatrix operator-(const IMatrix& m){
  return capd::vectalg::unaryMinus<IMatrix> (m);
}

// ---------------------------- matrix + matrix -------------------------------------

inline IMatrix operator+(const IMatrix& m1, const IMatrix& m2){
  return capd::vectalg::addObjects<IMatrix> (m1,m2);
}

// ---------------------------- matrix - matrix -------------------------------------

inline IMatrix operator-(const IMatrix& m1, const IMatrix& m2){
  return capd::vectalg::subtractObjects<IMatrix> (m1,m2);
}

// ---------------------------- matrix *,/ scalar -------------------------------------

inline IMatrix operator*(const IMatrix& m, const DInterval& s){
  return capd::vectalg::multiplyObjectScalar<IMatrix> (m,s);
}

inline IMatrix operator*(const DInterval& s, const IMatrix& m){
  return capd::vectalg::multiplyObjectScalar<IMatrix> (m,s);
}

inline IMatrix operator*(const IMatrix& m, const double s){
  return capd::vectalg::multiplyObjectScalar<IMatrix> (m,s);
}

inline IMatrix operator*(const double s, const IMatrix& m){
  return capd::vectalg::multiplyObjectScalar<IMatrix> (m,s);
}

inline IMatrix operator*(const IMatrix& m, const int s){
  return capd::vectalg::multiplyObjectScalar<IMatrix> (m,s);
}

inline IMatrix operator*(const int s, const IMatrix& m){
  return capd::vectalg::multiplyObjectScalar<IMatrix> (m,s);
}

inline IMatrix operator/(const IMatrix& m, const DInterval& s){
  return capd::vectalg::divideObjectScalar<IMatrix> (m,s);
}

inline IMatrix operator/(const IMatrix& m, const double s){
  return capd::vectalg::divideObjectScalar<IMatrix> (m,s);
}

inline IMatrix operator/(const IMatrix& m, const int s){
  return capd::vectalg::divideObjectScalar<IMatrix> (m,s);
}

// ---------------------------- matrix + scalar -------------------------------------

inline IMatrix operator+(const IMatrix& m, const DInterval& s){
  return capd::vectalg::addObjectScalar<IMatrix> (m,s);
}

// ---------------------------- matrix - scalar -------------------------------------

inline IMatrix operator-(const IMatrix& m, const DInterval& s){
  return capd::vectalg::subtractObjectScalar<IMatrix> (m,s);
}

// ------------------------- inequalities - true if hold true on each coord ---------

inline bool operator<(const IMatrix& m1, const IMatrix& m2){
  return capd::vectalg::lessThan(m1,m2);
}

inline bool operator>(const IMatrix& m1, const IMatrix& m2){
  return capd::vectalg::greaterThan(m1,m2);
}

inline bool operator<=(const IMatrix& m1, const IMatrix& m2){
  return capd::vectalg::lessEqual(m1,m2);
}

inline bool operator>=(const IMatrix&m1, const IMatrix&m2){
  return capd::vectalg::greaterEqual(m1,m2);
}

inline bool operator==(const IMatrix &a1,const IMatrix &a2){
  return capd::vectalg::equal(a1,a2);
}

inline bool operator!=(const IMatrix &a1,const IMatrix &a2){
  return capd::vectalg::notEqual(a1,a2);
}

//------------------------ assignments - Scalars ------------------------//

inline IMatrix& IMatrix::operator=(const DInterval &s){
  return capd::vectalg::assignFromScalar(*this,s);
}

inline IMatrix& IMatrix::operator+=(const DInterval &s){
  return capd::vectalg::addAssignObjectScalar(*this,s);
}

inline IMatrix& IMatrix::operator-=(const DInterval &s){
  return capd::vectalg::subtractAssignObjectScalar(*this,s);
}

inline IMatrix& IMatrix::operator*=(const DInterval &s){
  return capd::vectalg::multiplyAssignObjectScalar(*this,s);
}

inline IMatrix& IMatrix::operator/=(const DInterval &s){
  return capd::vectalg::divideAssignObjectScalar(*this,s);
}

//------------------------- assignments - matrices --------------------//

inline IMatrix& IMatrix::operator+=(const IMatrix& a){
  return capd::vectalg::addAssignObjectObject(*this,a);
}

inline IMatrix& IMatrix::operator-=(const IMatrix& a){
  return capd::vectalg::subtractAssignObjectObject(*this,a);
}

inline void ortonormalize(IMatrix & A, IVector &v){
   capd::matrixAlgorithms::orthonormalize(A,v);
}
}} // the end of the namespace capd::facade

#endif // _CAPD_FACADE_IMATRIX_H_

