/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Matrix.hpp
///
/// @author Marian Mrozek, Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_VECTALG_MATRIX_HPP_
#define _CAPD_VECTALG_MATRIX_HPP_

#include <vector>
#include <stack>

#include "capd/auxil/minmax.h"
#include "capd/vectalg/Matrix.h"

#include "capd/vectalg/Matrix_Interval.hpp"
#include "capd/vectalg/RowVector.hpp"
#include "capd/vectalg/ColumnVector.hpp"
#include "capd/vectalg/Vector.hpp"
#include "capd/basicalg/TypeTraits.h"

#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"


namespace capd{
namespace vectalg{


//-------------------------- constructors ------------------------//

template<typename Scalar, int rows, int cols>
Matrix<Scalar,rows,cols>::Matrix(const MatrixSlice<Matrix> &A_m)
   : ContainerType(A_m.numberOfRows(),A_m.numberOfColumns(),true)
{
  if(numberOfRows() && numberOfColumns()){
   for (int i=1; i<=numberOfRows(); ++i)
    for (int j=1; j<=numberOfColumns(); ++j)
      (*this)(i,j) = *A_m.at(i,j);
  }
}

template<typename Scalar, int rows, int cols>
Matrix<Scalar,rows,cols>::Matrix(Matrix<double,rows,cols>& a_m)
   : ContainerType(a_m.numberOfRows(),a_m.numberOfColumns(),true)
{
  std::copy(a_m.begin(),a_m.end(),begin());
}

template<typename Scalar, int rows, int cols>
Matrix<Scalar,rows,cols>::Matrix(int A_rows,int A_cols,const Scalar dane[]) : ContainerType(A_rows,A_cols,true)
{
  std::copy(dane,dane+this->size(),begin());
}

template<typename Scalar, int rows, int cols>
Matrix<Scalar,rows,cols>::Matrix(const Scalar dane[]) : ContainerType() {
  std::copy(dane,dane+this->size(),begin());
}

template<typename Scalar, int rows, int cols>
Matrix<Scalar,rows,cols>::Matrix(const char data[]) : ContainerType()
{
   std::istringstream str(data);
   str >> *this;
}
template<typename Scalar, int rows, int cols>
Matrix<Scalar,rows,cols>::Matrix(const std::string & data) : ContainerType()
{
   std::istringstream str(data);
   str >> *this;
}

//------------- operations on matrices -------------------------//

template<typename Scalar, int rows, int cols>
Matrix<Scalar,rows,cols> Matrix<Scalar,rows,cols>::Identity(int A_dimension)
{
   // the matrix is filled by zeros
   Matrix<Scalar,rows,cols> temp(A_dimension,A_dimension);
   for(int i=1;i<=A_dimension;++i)
      temp(i,i) = TypeTraits<ScalarType>::one();
   return temp;
}


template<typename Scalar, int rows, int cols>
void Matrix<Scalar,rows,cols>::setToIdentity()
{
   if(numberOfRows()!=numberOfColumns())
      throw std::range_error("Matrix<Scalar,rows,cols>::setToIdentity: rows!=cols");
   clear();
   for(int i=1;i<=numberOfRows();++i)
      (*this)(i,i) = TypeTraits<ScalarType>::one();
}


template<typename Scalar, int rows, int cols>
void Matrix<Scalar,rows,cols>::transpose()
{
   if(numberOfRows()!=numberOfColumns())
      throw std::runtime_error("Cannot call x.transpose() for nonsquare matrix");

   for(int i=1;i<=numberOfRows();++i)
   for(int j=i+1;j<=numberOfRows();++j)
   {
      Scalar a = (*this)(i,j);
      (*this)(i,j) = (*this)(j,i);
      (*this)(j,i) = a;
   }
}


template<typename Scalar, int rows, int cols>
Matrix<Scalar,cols,rows> transpose(const Matrix<Scalar,rows,cols> &a)
{
   Matrix<Scalar,cols,rows> temp(a.numberOfColumns(),a.numberOfRows(),true);
   for(int i=1;i<=a.numberOfColumns();++i)
      for(int j=1;j<=a.numberOfRows();++j)
         temp(i,j)= a(j,i);
   return temp;
}

template<typename Scalar, int rows, int cols>
inline Matrix<Scalar,cols,rows> Transpose(const Matrix<Scalar,rows,cols> &a){
  return transpose(a);
}
// ----------------- input - output ------------------------------ //

template<typename Scalar, int rows, int cols>
std::ostream &operator<<(std::ostream &out,const Matrix<Scalar,rows,cols> &a)
{
   out << "{";
   if(a.numberOfColumns()>0){
     if(a.numberOfRows()>1) out << std::endl;
     if(a.numberOfRows()>0) out << a[0];
     for(int i=1;i<a.numberOfRows();++i)
     {
        out << "," << std::endl << a[i];
     }
     if(a.numberOfRows()>1) out << std::endl;
   }
   out << "}";
   return out;
}


template<typename Scalar, int rows, int cols>
std::istream &operator>>(std::istream &inp, Matrix<Scalar,rows,cols> &a){
  typedef typename Matrix<Scalar,rows,cols>::RowVectorType VectorType;
  std::stack<VectorType> st;
  VectorType v(cols);
  int ch=0,dimension=0;
  while('{'!=(ch=inp.get()) && ch!=EOF);
  if(ch!=EOF){
    while(' '==(ch=inp.peek()) || ch=='\n') inp.get();
    if(ch!='}'){ // otherwise we have an ampty matrix
      inp >> v;
      st.push(v);
      dimension=v.dimension();
      do{
        do{
          ch=inp.get();
        }while(ch==' ' || ch=='\t' || ch=='\n');
        if(ch==','){
          inp >> v;
          if(dimension!=v.dimension())
            throw std::ios_base::failure("Rows of incompatible dimensions found when reading a matrix");
          st.push(v);
        }
      }while(ch!='}' && ch!=EOF);
    }
  }

  int n = static_cast<int>(st.size());
  a.resize(n,dimension);
  for(int i=n-1;i>=0;--i)
  {
    v=st.top();
    a[i]=v;
    st.pop();
  }

  if(inp.eof())
    throw std::ios_base::failure("EOF encountered when reading a matrix");
  return inp;
}

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_MATRIX_HPP_

/// @}
