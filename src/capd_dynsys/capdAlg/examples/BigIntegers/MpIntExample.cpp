/**

 *  @file MpIntExample.cpp
 *
 *  @author kapela  @date 2010-09-17
 */


#include <iostream>
#include <cstdlib>
#include <ctime>

// We include definitions of MpInt MpZVector MpZMatrix
#include "capd/vectalg/mplib.h"

// these are
// typedef mpz_class MpInt;
// typedef capd::vectalg::Vector<MpInt,DIM> MpZVector;
// typedef capd::vectalg::Matrix<MpInt,DIM,DIM> MpZMatrix;

using namespace std;
using namespace capd;

int main(int argc, char **argv) {
  int dim = 4;
  MpZMatrix A(dim, dim),
           Q(dim, dim), Q_1(dim, dim),
           R(dim, dim), R_1(dim, dim);
  int s, t;
  srand(time(0));
  for(int i=1; i<dim+1; ++i)
    for(int j=1; j<dim+1; ++j)
      A(i,j) = rand();
  MpZMatrix  B = A;

  // We take a random matrix A and bring it to the Smith form
  //   Q, Q_1, R, R_1 will contain coordinate changes
  capd::matrixAlgorithms::smithForm(A, Q, Q_1, R, R_1, s, t);


  cout << "\n matrix : " << B
       << "\n result : " << A
       << "\n test   : " << Q*A*R_1-B;  // should be zero

  return 0;
}
