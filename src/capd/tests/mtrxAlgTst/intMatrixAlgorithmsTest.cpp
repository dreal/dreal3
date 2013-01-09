/// @addtogroup matrixAlgorithms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file intMatrixAlgorithmsTest.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <cassert>
#include <sstream>
#include "capd/capd/debuger.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"

using namespace std;
using namespace capd::matrixAlgorithms;
using namespace capd::vectalg;

void rowEchelonTest(){
  int dane[]={
               3,2,1,4,
               2,3,1,-1,
               4,4,-2,-2,
             };
  const int m=3;
  const int n=4;
  Matrix<int,0,0> A(m,n,dane);
  Matrix<int,0,0> B(m,n,dane);
  Matrix<int,0,0> Q(m,m),Qinv(m,m);
  int k;


  rowEchelon(B,Q,Qinv,k);

  cout << "\n\n === Row Echelon Test ==== \n\n";
  cout << "A=" << A << "\n\n";
  cout << "Row echelon of A is B=" << B << "\n";
  cout << "In the base Q=" << Q << "\n";
  cout << "The number of nonzero rows is " << k << "\n";
  cout << "The inverse of the matrix Q is Qinv=" << Qinv << "\n\n";

  cout << "Testing correctness: \n";

  assert(!nonZero(Q*Qinv - Matrix<int,0,0>::Identity(m)));
  assert(!nonZero(Qinv*Q - Matrix<int,0,0>::Identity(m)));
  assert(!nonZero(Qinv*A - B));
  assert(!nonZero(Q*B - A));
}

void columnEchelonTest(){
  int dane[]={
    0,2,2,
    1,0,-1,
    3,4,1,
    5,3,-2
  };
  const int m=4;
  const int n=3;
  Matrix<int,0,0> A(m,n,dane);
  Matrix<int,0,0> B(A);
  Matrix<int,0,0> R(n,n),Rinv(n,n);
  int k;
  columnEchelon(B,R,Rinv,k);

  cout << "\n\n === Column Echelon Test ==== \n\n";
  cout << "A=" << A << endl;
  cout << "Column echelon form of A is: \n";
  cout << "B=" << B << endl;
  cout << "Number of nonzero columns in column echelon form is: \n";
  cout << "k=" << k << endl;
  cout << "New base in the domain consists of columns of \n";
  cout << "R=" << Rinv << endl;

  cout << "Testing correctness: \n";
  assert(!nonZero(R*Rinv - Matrix<int,0,0>::Identity(n)));
  assert(!nonZero(Rinv*R - Matrix<int,0,0>::Identity(n)));
  assert(!nonZero(A*Rinv - B));
  assert(!nonZero(B*R - A));

}

void kernelImageTest(){
  int dane[]={
    0,2,2,
    1,0,-1,
    3,4,1,
    5,3,-2
  };
  const int m=4;
  const int n=3;
  Matrix<int,0,0> A(m,n,dane);
  Matrix<int,0,0> B(A);
  Matrix<int,0,0> kernel,image;
  kernelImage(B,kernel,image);


  cout << "\n\n === Kernel Image Test ==== \n\n";
  cout << "A=" << A << endl;
  cout << "Column echelon form of A is: \n";
  cout << "B=" << B << endl;
  cout << "Kernel base is: \n";

  for(int j=0;j<kernel.numberOfColumns();++j)
    cout << kernel.column(j) << endl;

  cout << "Image base is: \n";
  for(int j=0;j<image.numberOfColumns();++j)
    cout << image.column(j) << endl;
}

void smithFormTest(){
    int dane[]={
                 3,2,3,7,1,2,7,8,9,0,
                 0,2,0,1,2,4,6,3,2,3,
                 2,2,2,6,0,9,7,2,3,1,
                 4,5,2,7,8,4,5,0,1,1,
                 5,6,3,8,0,1,2,3,1,0,
                 6,3,7,5,0,9,2,1,4,3,
                 5,2,3,1,8,4,5,0,2,1,
                 0,5,3,7,5,1,2,0,9,9,
                 1,1,1,9,9,0,8,9,6,5,
                 6,4,8,7,4,0,8,9,1,3
               };
    const int m=10;
    const int n=10;

    Matrix<int,0,0> A(m,n,dane);
    Matrix<int,0,0> B(m,n,dane);
    Matrix<int,0,0> Q(m,m);
    Matrix<int,0,0> Qinv(m,m);
    Matrix<int,0,0> R(n,n);
//    Matrix<int,0,0> R;
    Matrix<int,0,0> Rinv(n,n);
//    Matrix<int,0,0> Rinv;

    int t,s;

    smithForm(B,Q,Qinv,R,Rinv,s,t);

    cout << "\n\n === Smith Form Test ==== \n\n";
    cout << "A=" << A << "\n\n";
    cout << "\n\nSmith form of A is B=" << B << "\n";
    cout << "in bases:\n";
    cout << "Q=" << Q << "\n";
    cout << "R=" << R << "\n";
    cout << " Number of nonzero elements on diagonal=" << t << "\n";
    cout << " Number of units on diagonal=" << s << "\n\n";


    cout << "The inverses of bases are:\n";
    cout << "Qinv=" << Qinv << "\n";
    cout << "Rinv=" << Rinv << "\n\n";

    cout << " Testing correctness:\n";

    ostringstream o;
    o << B;
//    assert(o.str() == "{{1,0,0,0,0,0,0,0,0,0},{0,1,0,0,0,0,0,0,0,0},{0,0,1,0,0,0,0,0,0,0},{0,0,0,1,0,0,0,0,0,0},{0,0,0,0,1,0,0,0,0,0},{0,0,0,0,0,1,0,0,0,0},{0,0,0,0,0,0,1,0,0,0},{0,0,0,0,0,0,0,1,0,0},{0,0,0,0,0,0,0,0,1,0},{0,0,0,0,0,0,0,0,0,119664800}}");

    assert(!nonZero(Q*Qinv - Matrix<int,0,0>::Identity(m)));
    assert(!nonZero(Qinv*Q - Matrix<int,0,0>::Identity(m)));
    assert(!nonZero(R*Rinv - Matrix<int,0,0>::Identity(n)));
    assert(!nonZero(Rinv*R - Matrix<int,0,0>::Identity(n)));
    assert(!nonZero(Qinv*A*R - B));
    assert(!nonZero(Q*B*Rinv - A));
}

void solveLinearEquationTest(){
    int dane[]={
                 3,2,3,
                 0,2,0,
                 2,2,2
               };
//    int bDane[]={-6,10,0};
    int bDane[]={2,8,4};
    const int m=3;
    const int n=3;

    Matrix<int,0,0> A(m,n,dane);
    Vector<int,0> b(3,bDane),x;

    bool result=solveLinearEquation(A,b,x);

    cout << "\n\n === Linear Equation Test ==== \n\n";
    cout << "A=" << A << "\n";
    cout << "b=" << b << "\n";
    if(result){
      cout << "Found solution x=" << x << endl;
    }else{
      cout << "No solution found\n";
    }
    cout << " Testing correctness:\n";
    cout << " The difference should be a zero vector " << A*x - b << ":\n";
    assert(A*x == b);
    int d[]={3};
    Matrix<int,0,0> U(1,1,d);
    cout << U << "\n";
    cout << Matrix<int,0,0>(U) << "\n";
}

int main(int argc, char* argv[]){
  try{
    rowEchelonTest();
    columnEchelonTest();
    kernelImageTest();
    smithFormTest();
    solveLinearEquationTest();
  }catch(std::exception& e){
    std::cout << "Exception caught: " << e.what() << std::endl;
  }catch(const char *c){
    cout << "Exception caught: " << c << endl;
  }catch(...){
    cout << "Unknown Exception caught: " << endl;
  }

  return 0;
}

/// @}
