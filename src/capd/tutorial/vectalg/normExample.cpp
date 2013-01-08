/*
   author: Daniel Wilczak, Sept. 2007
   the file provides a quick tutorial on using template class Norm from capd library
*/

#include <iostream>
#include "capd/interval/DoubleInterval.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/vectalg/Norm.hpp"

// The template class Norm has two parameters - type of vector and type of matrix of which norms will be computed. 
// Class Norm is an abstract class which defines two purely virtual operators for computing norm of a vector and matrix.

// uncomment one of the following lines
typedef interval Scalar;
//typedef double Scalar;

// the following lines define new names for vectors and matrices of an arbitrarily dimensions
typedef capd::vectalg::Vector<Scalar,0> DVector;
typedef capd::vectalg::Matrix<Scalar,0,0> DMatrix;

int main(int, char**)
{
   try{
// --------------------------------- norms of vectors and matrices ------------------------------------------

      std::cout.precision(20);
      std::cout << "Norms of vectors and matrices\n--------------------------------\n\n";
      // we create a matrix
      Scalar data[] = {-10.,1.,1.,1.,2.,-20.,0.,-1.,1.,2.,-30.,4.,3.,1.,2.,0.};
      DMatrix P(4,4,data);
      DVector v = P.row(0);
      // class norm has two template parameters - type of vector and type of matrix
      // below we create objects of three basic norms
      capd::vectalg::EuclNorm<DVector,DMatrix> euclNorm;
      capd::vectalg::MaxNorm<DVector,DMatrix> maxNorm;
      capd::vectalg::SumNorm<DVector,DMatrix> sumNorm;
      
      // now we can compute norms of vectors and matrices
      std::cout << "P=" << P << std::endl;
      std::cout << "v=" << v << std::endl << std::endl;
      
      std::cout << "EuclNorm(P)=" << euclNorm(P) << std::endl;
      std::cout << "EuclNorm(v)=" << euclNorm(v) << std::endl << std::endl;

      std::cout << "MaxNorm(P)=" << maxNorm(P) << std::endl;
      std::cout << "MaxNorm(v)=" << maxNorm(v) << std::endl << std::endl;

      std::cout << "SumNorm(P)=" << sumNorm(P) << std::endl;
      std::cout << "SumNorm(v)=" << sumNorm(v) << std::endl << std::endl;


      std::cout << "Logarithmic norms of vectors and matrices\n--------------------------------\n\n";
      capd::vectalg::EuclLNorm<DVector,DMatrix> euclLogNorm;
      capd::vectalg::MaxLNorm<DVector,DMatrix> maxLogNorm;
      capd::vectalg::SumLNorm<DVector,DMatrix> sumLogNorm;

      std::cout << "EuclLogNorm(P)=" << euclLogNorm(P) << std::endl;
      std::cout << "EuclLogNorm(v)=" << euclLogNorm(v) << std::endl << std::endl;

      std::cout << "MaxLogNorm(P)=" << maxLogNorm(P) << std::endl;
      std::cout << "MaxLogNorm(v)=" << maxLogNorm(v) << std::endl << std::endl;

      std::cout << "SumLogNorm(P)=" << sumLogNorm(P) << std::endl;
      std::cout << "SumLogNorm(v)=" << sumLogNorm(v) << std::endl << std::endl;
      
   }catch(std::exception& e)
   {
      std::cout << e.what();
   }
   return 0;
}
