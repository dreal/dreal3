/*
   author: Daniel Wilczak, Sept. 2007
   the file presents algorithms from matrixAlgorithms module
*/

#include <iostream>
#include "capd/interval/DoubleInterval.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"

// the module matrixAlgorithms implements several algoritms for manipulating on matrices
// and solving equations, like Gauss elimination, QR-decomposition. LU-decomposition
// all algorithms are template functions and unique template parameter is MatrixType

using namespace capd::vectalg;
using namespace capd::matrixAlgorithms;

// uncomment one of the following lines
typedef double Scalar;
//typedef interval Scalar;

// the following lines define new names for vectors and matrices of ana arbitrarily dimensions
typedef Vector<Scalar,0> DVector;
typedef Matrix<Scalar,0,0> DMatrix;


int main(int, char**)
{
   try{
      std::cout.precision(20);
      // we create a matrix
//      Scalar data[] = {1,2,1,2,2,2,2,0,1,2,3,4,1,1,1,1};
      Scalar data[] = {1,2,1,2,2,2,2,0,1,97,3,4,1,19,1,15};
      DMatrix P(4,4,data);
      DMatrix S = (P+Transpose(P))/Scalar(2.); // symmatrization of P
      DVector v = P.row(0);
      std::cout << "P=" << P << std::endl;
      std::cout << "v=" << v << std::endl;
      
// ------------------------------ Gauss elimination -------------------------------------------

      std::cout << "\nGauss elimination\n--------------------------------\n\n";
      // the Gauss elimination is realized by function gauss. It has two parameters - a matrix M and vector v
      // It returns M^{-1}*v or throws an exception when computation of result is imposible
      
      DVector gaussResult = gauss(P,v);
      std::cout << "gauss(P,v)=" << gaussResult << std::endl;
      std::cout << "verification of the result:\nP*gauss(P,v)=" << P*gaussResult << std::endl;

// ------------------------------ Orthonormalization -------------------------------------------

      std::cout << "\nOrthonormalization\n--------------------------------\n\n";
      // this algorithm computes an orthogonal matrix from a given matrix
      // First the columns are sorted by decreasing norm and next Gramm-Schmidt algorithm 
      // is applied.
      DMatrix Q = P;
      orthonormalize(Q);
      std::cout << "Q=orthonormalize(P)=" << Q << std::endl;
      // Q should be orthogonal, hence Q*Q^T should be Id matrix
      std::cout << "verification of the result:\nQ*Transpose(Q)=" << Q*Transpose(Q) << "\nshould be identity matrix" << std::endl;

// ------------------------------ QR decomposition -------------------------------------------

      std::cout << "\nQR decomposition\n--------------------------------\n\n";
      // this algorithm performs QR decomposition of a given square matrix
      // as a result we obtain orthogonal and upper traingular matrix
      // first argument of the function is a matrix to decompose
      // other two are resulting matrices Q and R, respectively
      DMatrix R(4,4);
      QR_decompose(P,Q,R); 
      // P should be equal to Q*R
      std::cout << "QR decomposition of P:" << std::endl;
      std::cout << "Q=" << Q << std::endl;
      std::cout << "R=" << R << std::endl;
      std::cout << "verification if P-Q*R is close to zero\n";
      std::cout << "P-Q*R=" << P-Q*R << std::endl;
      std::cout << "verification if Q is orthogonal:\n";
      std::cout << "Q*Transpose(Q)=" << Q*Transpose(Q) << std::endl;
      
// ------------------------------ diagonalization -------------------------------------------
   
      std::cout << "\nDiagonalization\n--------------------------------\n\n";
      // the following function implements Jacobi rotation algorithm for computing 
      // of diagonalization of a symmetric matrix
      // in this example we diagonalize 0.5*(P+P^T)
      // the last argument is a diagonalization tolerance, by default is set to 1e-5
      symMatrixDiagonalize(S,R,1e-10);
      std::cout << "Diagonalization of 0.5*(P+P^T)=" << R << std::endl;

// ------------------------------ spectral radius -------------------------------------------
   
      std::cout << "\nSpectral radius \n--------------------------------\n\n";
      // the following function computes upper bound for special radius of a symmetric matrix
      std::cout << "spectralRadiusOfSymMatrix(0.5*(P+P^T))=" << spectralRadiusOfSymMatrix(S) << std::endl;

// ------------------------------ max eigenvalue -------------------------------------------

      std::cout << "\nMaximal eigenvalue \n--------------------------------\n\n";
      // this function computes upper bound for maximal eigenvalue of a symmetric matrix
      // first it computes matrix which has the same eigenvalues and which is close to diagonal,
      // next upper bound is computed from Gerschgorin theorem
      std::cout << "maxEigenValue(0.5*(P+P^T))=" << maxEigenValueOfSymMatrix(S) << std::endl;

// ------------------------------ inverse matrix -------------------------------------------

      std::cout << "\nInverse matrix \n--------------------------------\n\n";
      // there are two algorithms which compute an inverse matrix
      // first decomposes a matrix A=Q*R, where Q-orthogonal, R-upper diagonal
      // and compute A^{-1} = R^{-1}*Q^T
      DMatrix invP = inverseMatrix(P);
      std::cout << "Inverse of P by using QR-decomposition:" << invP << std::endl;
      std::cout << "verification: P*inverseMatrix(P)=" << P*invP << std::endl;

      //second algorithm computes inverse matrix by using Gauss elimination
      invP = gaussInverseMatrix(P);
      std::cout << "Inverse of P by using Gauss elimination:" << invP << std::endl;
      std::cout << "verification: P*gaussInverseMatrix(P)=" << P*invP << std::endl;
      
   }catch(std::exception& e)
   {
      std::cout << e.what();
   }
   return 0;
}
