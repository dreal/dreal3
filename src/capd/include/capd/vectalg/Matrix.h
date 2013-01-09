/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Matrix.h
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

#ifndef _CAPD_VECTALG_MATRIX_H_
#define _CAPD_VECTALG_MATRIX_H_

#include <iostream>
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/RowVector.h"
#include "capd/vectalg/ColumnVector.h"
#include "capd/vectalg/MatrixContainer.h"
#include "capd/vectalg/MatrixIterator.h"
#include "capd/vectalg/MatrixSlice.h"


namespace capd{
namespace vectalg{

template<typename Scalar, int rows, int cols>
class Matrix;

template<typename Scalar, int rows,int cols1, int cols2>
Matrix<Scalar,rows,cols2> operator*(const Matrix<Scalar,rows,cols1>&, const Matrix<Scalar,cols1,cols2>&);

template<typename Scalar, int rows,int cols>
Matrix<Scalar,cols,rows> transpose(const Matrix<Scalar,rows,cols>&);

//Deprecated
template<typename Scalar, int rows,int cols>
Matrix<Scalar,cols,rows> Transpose(const Matrix<Scalar,rows,cols>&);

template<typename Scalar, int rows,int cols>
std::ostream &operator<<(std::ostream&, const Matrix<Scalar,rows,cols>&);

template<typename Scalar, int rows,int cols>
std::istream &operator>>(std::istream&, Matrix<Scalar,rows,cols>&);

template<typename IMatrixType>
IMatrixType midMatrix(const IMatrixType& v);

// ########################################################################### //

template<typename Scalar, int rows, int cols>
class Matrix : public MatrixContainer<Scalar,rows,cols>
{
public:
  typedef Scalar ScalarType;
  typedef MatrixContainer<Scalar,rows,cols> ContainerType;
  typedef typename ContainerType::iterator iterator;
  typedef typename ContainerType::const_iterator const_iterator;
  typedef typename ContainerType::Dimension Dimension;

  typedef Vector<Scalar,cols> RowVectorType;
  typedef Vector<Scalar,rows> ColumnVectorType;
  typedef RowVector<Scalar,cols> RefRowVectorType;
  typedef ColumnVector<Scalar,rows> RefColumnVectorType;
  typedef Matrix<Scalar,rows,cols> MatrixType;

  //constructors
  Matrix();
  Matrix(int A_rows,int A_cols);               //assigns 0 to every coordinate
  Matrix(const ScalarType data[]);
  Matrix(int A_rows,int A_cols, const ScalarType data[]);
  Matrix(const Matrix& m);                     // copying constructor
  Matrix(const MatrixSlice<MatrixType>& m);    // copying from matrix slice
  Matrix(Matrix<double,rows,cols>&);
  Matrix(const Dimension& A_dim);           //assigns 0 to every coordinate
  Matrix(const Dimension& d,bool);
  Matrix(int A_rows,int A_cols,bool);
  void clear();                                //assigns zero to each coord

  //assignments - matrices
  Matrix& operator= (const Matrix& a);         //assign a matrix
  Matrix& operator+=(const Matrix& a);         //increase by a matrix
  Matrix& operator-=(const Matrix& a);         //decrease by a matrix

  //assignments - Scalars
  Matrix& operator= (const Scalar& s);         //assign a Scalar
  Matrix& operator+=(const Scalar& s);         //increase by a Scalar
  Matrix& operator-=(const Scalar& s);         //decrease by a Scalar
  Matrix& operator*=(const Scalar& s);         //rescale by multiplying
  Matrix& operator/=(const Scalar& s);         //rescale by dividing

  // iterator selections
  MatrixIterator< MatrixType > beginMatrix();
  MatrixIterator< MatrixType > endMatrix();
  MatrixIterator< MatrixType > beginOfRow(int i);
  MatrixIterator< MatrixType > beginOfColumn(int j);
  MatrixIterator< MatrixType > endOfRow(int i);
  MatrixIterator< MatrixType > endOfColumn(int j);

  const_MatrixIterator< MatrixType > beginMatrix() const;
  const_MatrixIterator< MatrixType > endMatrix() const;
  const_MatrixIterator< MatrixType > beginOfRow(int i) const;
  const_MatrixIterator< MatrixType > beginOfColumn(int j) const;
  const_MatrixIterator< MatrixType > endOfRow(int i) const;
  const_MatrixIterator< MatrixType > endOfColumn(int j) const;

  using ContainerType::begin;
  using ContainerType::end;

  //indexing
  RowVector<Scalar,cols> operator[](int i) const; // i-th row as a vector
  RowVector<Scalar,cols> operator()(int i) const; // (i-1)-th row as a vector
  Scalar& operator()(int i,int j);                 //returns reference to the [i-1][j-1] entry
  const Scalar& operator()(int i,int j) const;     //returns const reference to the [i-1][j-1] entry
  Scalar* at(int i,int j);                         //returns pointer to the [i-1][j-1] entry
  const Scalar* at(int i,int j) const;             //returns pointer to the [i-1][j-1] entry

  //operations on matrices
  static Matrix Identity(int dimension);              // returns the identity matrix
  void setToIdentity();                               // if square matrix, changes it to the identity matrix
  RowVector<Scalar,cols> row(int i) const;       // i-th row as a vector
  ColumnVector<Scalar,rows> column(int j) const; // returns j-th column
  void transpose();

  int rowStride()const {
    return numberOfColumns();
  } // difference of pointers when moving to the next row in the same column
  int columnStride()const{
    return 1;
  }  // difference of pointers when moving to the next column in the same row

  using ContainerType::numberOfRows;
  using ContainerType::numberOfColumns;
  using ContainerType::dimension;

  friend std::istream &operator>> <> (std::istream &inp, MatrixType &a);

// Deprecated
   void Transpose() { transpose(); }

protected:
  using ContainerType::resize;
  using ContainerType::data;
}; //the end of class Matrix

}} // namespace capd::vectalg

#include "capd/vectalg/Matrix_inline.h"

#endif // _CAPD_VECTALG_MATRIX_H_

/// @}
