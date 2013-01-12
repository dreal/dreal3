#include "capd/facade/capdAlglib.h"
#include "capd/matrixAlgorithms/capd2alglib.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"
#include <iostream>

using namespace capd;
using namespace capd::facade;

int main(){ 
  
  { // 2x2 matrix with complex eigenvalues

  DMatrix A(2,2);
  A[0][0] = 2;      A[0][1] = 10;
  A[1][0] = -10;    A[1][1] = 2;
                                // place for an output:
  DVector rV(2), iV(2);         // real and imaginary parts of eigenvalues

  capd::alglib::computeEigenvalues(A,rV,iV);

	std::cout << "\nmatrix A  = \n" << A;
  std::cout << "\neigenValues = " << capd::alglib::eigenvaluesToString(rV, iV, ", ");
  }
	{ //##############################################################
    // 2x2 matrix with real eigenvalues
	DMatrix A(2,2);
	A[0][0] = 5;    A[0][1] = 1;
  A[1][0] = 3;    A[1][1] = 6;
  
                                // place for an output:
  DVector rV(2), iV(2);         // real and imaginary parts of eigenvalues
  DMatrix rVec(2,2), iVec(2,2); // real and imaginary parts of eigenvectors
  capd::alglib::computeEigenvaluesAndEigenvectors(A,rV,iV,rVec,iVec);
  
  std::cout << "\n======================="
            << "\nmatrix A  = \n " << A 
            << "\neigenValues = " << alglib::eigenvaluesToString(rV, iV, ", ");
  std::cout << "\neigenVectors : " << alglib::eigenvectorsToString(rVec, iVec);
  std::cout << "\neigenVectors (i-th column contains vector corresponing to i-th eigenvalue)= \n"
            << rVec << "+ i* " << iVec;
  std::cout << "\nCHECK (matrix A in the eigenvectors base - should be diagonal up to rounding errors):\n " 
            << capd::matrixAlgorithms::gaussInverseMatrix(rVec)*A*rVec;
	}
  //##############################################################
  // 3x3 diagonal matrix 
  double data[] = {1, 0, 0, 
                   0, 3, 0, 
                   0, 0, 7};
  // new coordinates base                    
  double base[] = {3, 1, 4,
                   2, -5, 3,
                   1, 4, 1}; 
  DMatrix B(3,3, data), P(3,3, base);
  // C is a matrix B in new coordinates 
  DMatrix C = capd::matrixAlgorithms::gaussInverseMatrix(P)*B*P;
  
  // Place for output:
  DVector eigReal(3), eigIm(3);  // real and imaginary parts of eigenvalues
  DMatrix Vreal(3,3), Vim(3,3);  // real and imaginary parts of eigenvectors (stored in corresponding columns)

  capd::alglib::computeEigenvaluesAndEigenvectors(C, eigReal, eigIm, Vreal, Vim);
  
  std::cout << "\n======================="
            << "\nmatrix C = \n" << C << "\neigenvalues of C = " << alglib::eigenvaluesToString(eigReal, eigIm)
            << "\neigenvectors of C\n" << alglib::eigenvectorsToString(Vreal,Vim)
            << std::endl;
 
	return 0;
}
