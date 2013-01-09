/*
   author: Daniel Wilczak, Sept. 2007
   the file provides a quick tutorial on using template class Matrix from capd library
*/

#include <iostream>
#include "capd/interval/DoubleInterval.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"

using namespace capd::vectalg;

// the template class Matrix has three parameters - type which is stored in a matrix, number of rows and number of columns
// template class Matrix<typename ScalarType,int rows, int cols>
// if both arguments rows and cols are greater than zero, the matrix is represented as an internal one-dimensional array 
// with suitable indexing
// if rows or cols is equal to zero, the matrix has a pointer to allocated array

// the following lines define new names for four dimensional vectors 
typedef Vector<double,4> DVector4D;
typedef Vector<interval,4> IVector4D;

// the following lines define new names for vectors of ana arbitrarily length
typedef Vector<double,0> DVector;
typedef Vector<interval,0> IVector;

// the following lines define new names for square matrices 4x4 both for doubles and intervals
typedef Matrix<double,4,4> DMatrix4D;
typedef Matrix<interval,4,4> IMatrix4D;

// the following lines define new names for matrices with an arbitrary size
typedef Matrix<double,0,0> DMatrix;
typedef Matrix<interval,0,0> IMatrix;

int main(int, char**)
{
   try{
// --------------------------------- how to create a matrix ---------------------------------------------

      std::cout << "How to create a matrix\n--------------------------------\n\n";

      // the following line creates a 4x4 matrix filled by zeros
      DMatrix4D M;
      // matrix N will be a 4x5 dimensional interval matrix filled by zeros
      IMatrix N(4,5);
      std::cout << "M=" << M << std::endl;
      std::cout << "N=" << N << std::endl;

      double data[] = {1.,2.,3.,4.,4.,3.,2.,1.,1.,2.,3.,4.};
      // the following line creates a matrix from a given table of numbers
      // the number of elements in a table should be greater or equal to the number of coefficients in created matrix
      // table should contain following rows of the matrix
      const DMatrix P(3,4,data);
      DMatrix Q(4,3,data);
      std::cout << "P=" << P << std::endl;
      std::cout << "Q=" << Q << std::endl;

// --------------------------------- arrays of matrices --------------------------------------------------

      std::cout << "\n\nHow to create an array of matrices\n--------------------------------\n\n";

      // when one needs create an array of matrices which have undefined size at compilation time, 
      // the following solution is available.
      DMatrix *tab = new (2,4) DMatrix[10];
      // which means that tab contains an adress of a table of ten matrices, each of size 2x4
      std::cout << "Number of rows of matrices in array is: " << tab[0].numberOfRows() << std::endl;
      std::cout << "Number of columns of matrices in array is: " << tab[0].numberOfColumns() << std::endl;
      delete []tab;

      // when the same mathod is applied to the matrices of fixed dimensions, there is no effect
      DMatrix4D *tab2 = new (5,6) DMatrix4D[5];
      std::cout << "Number of rows of matrices in array is: " << tab2[0].numberOfRows() << std::endl;
      std::cout << "Number of columns of matrices in array is: " << tab2[0].numberOfColumns() << std::endl;
      delete []tab2;

// --------------------------------- indexing ------------------------------------------------------------

      std::cout << "\n\nIndexing\n--------------------------------\n\n";
      
      // one can change or access a coefficient in matrix by using of operator() or iterators
      std::cout << "operator() : \n";
      for(int i=1;i<=P.numberOfRows();++i)
      {
         for(int j=1;j<=P.numberOfColumns();++j)
         {
            std::cout << "P(" << i << "," << j << ")=" << P(i,j) << std::endl;
            //one can set a coefficient in nonconstant matrix
            Q(j,i) = i*j;
            std::cout << "New value of Q(" << j << "," << i << ")=" << Q(j,i) << std::endl;
         }
      }

// ---------------------------- rows and columns as vectors -------------------------------------------

      std::cout << "\n\nRows and columns of matrices as vectors\n--------------------------------\n\n";
      // the rows and columns of a matrix can be seen as vectors
      // the vectalg module provides two classes RowVector and ColumnVector which 
      // can be use as a reference to rows and columns of matrices. Objects of these classes have not their own memory
      // but only a pointer to a proper coefficient in a matrix.
      // These classes has almost the same properties as class Vector (iterators, indexing, normalization, etc), hence they can be used as vectors in 
      // generic algorithms
      std::cout << "Reference to first row of matrix Q: " << Q.row(0) << std::endl;
      std::cout << "Reference to first column of matrix Q: " << Q.column(0) << std::endl;
      Q.row(0).normalize();
      std::cout << "After normalization of first row of matrix Q:" << std::endl;
      std::cout << "Q=" << Q << std::endl;
      

// ---------------------------- iterators -------------------------------------------------------------

      std::cout << "\n\nContainerIterators\n--------------------------------\n\n";

      // class Matrix provides two iterators - low level for container for coefficients 
      // and MatrixIterator which is usefull for matrix algorithms
      // The following can be used for printing all coefficients in a matrix
      // functions begin and end return low level iterators for container
      // functions beginMatrix and endMatrix return matrix iterators
      DMatrix::iterator b = Q.begin(), e = Q.end();
      while(b!=e)
      {
         std::cout << "value of an iterator: " << b << "\ncoefficient in a matrix: " << (*b) << std::endl;
         ++b;
      }

      // in a similar way are defined const iterators for constant objects
      
      DMatrix::const_iterator p = P.begin(), k = P.end();
      std::cout << "\nCoefficients in constant matrix:\n";
      while(p!=k)
      {
         std::cout << (*p) << std::endl;
         ++p;
      }

// --------------------------------- MatrixIterator -----------------------------------------------------------

      std::cout << "\n\nMatrixIterators\n--------------------------------\n\n";
   // class Matrix provides a MatrixIterator for manipulating on coefficients in a matrix
   // the following operations are available
   
   
   MatrixIterator<DMatrix> i = P.beginMatrix();
   std::cout << "value pointed by iterator in matrix P: " << (*i) << std::endl;
   i.moveToNextRow();
   std::cout << "value pointed by iterator after moving to next row: " << (*i) << std::endl;
   i.moveToNextColumn();
   std::cout << "value pointed by iterator after moving to next column: " << (*i) << std::endl;
   

// --------------------------------- basic operations on matrices ---------------------------------------------
      
      std::cout << "\n\nBasic operation on matrices\n--------------------------------\n\n";
      // the following operations on matrices are available
      DMatrix R = Transpose(Q);
      std::cout << "P=" << P << std::endl;
      std::cout << "Q=" << Q << std::endl;
      std::cout << "R=" << R << std::endl;
      std::cout << "P+R=" << (P+R) << std::endl;
      std::cout << "P-R=" << (P-R) << std::endl;
      std::cout << "Q*R=" << (Q*R) << std::endl;
      std::cout << "2*P=" << 2.*P << std::endl;
      std::cout << "Q*R.column(0)=" << Q*R.column(0) << std::endl;
      std::cout << "if P==R? " << (P==R) << std::endl  << std::endl;
      // moreover, the standard operations like +=, -= etc. when possible are available

// ------------------------------------- other functions ------------------------------------------------------

      std::cout << "\n\nMember functions\n--------------------------------\n\n";
      DMatrix Z = Q*R;
      Z.Transpose();
      std::cout << "Z=Q*R; Z.Transpose() - transposes a square matrix " << Z << std::endl;
      Q.clear();
      std::cout << "Q.clear() - assign zero to each coefficient" << Q << std::endl;
      std::cout << "static function DMatrix::Identity(int) - returns an identity matrix of given dimension\n";
      std::cout << DMatrix::Identity(4) << std::endl;

// --------------------------------- operations for interval matrices only -------------------------------------
   
      std::cout << "\n\nOperations for interval matrices only\n--------------------------------\n\n";
      interval d1[] = {interval(-1.,1.),interval(2.,2.),interval(3.,3.1), interval(4.,4.1)};
      IMatrix v1(2,2,d1);
      IMatrix v2(2,2);
      std::cout << "v1=" << v1 << std::endl;
      // center of a matrix
      std::cout << "midMatrix(v1) = " << midMatrix(v1) << std::endl;

      // splitting: v2 = v1-midMatrix(v1) and v1 = midMatrix(v1). This operation is given by function 
      split(v1,v2);      
      std::cout << "\nafter calling split(v1,v2) we get\n";
      std::cout << "v1=" << v1 << std::endl;
      std::cout << "v2=" << v2 << std::endl;

      // for more details see the header file "vectalg/Matrix.h"
      // for algorithms on matrices (Gauss, QR, etc. see 'matrixAlgorithms' directory)
   }catch(std::exception& e)
   {
      std::cout << e.what();
   }
   return 0;
}
