/// @addtogroup newton
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file krawczyk.hpp
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_NEWTON_KRAWCZYK_HPP_ 
#define _CAPD_NEWTON_KRAWCZYK_HPP_ 

#include <stdexcept>
#include "capd/newton/Krawczyk.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

namespace capd{
namespace newton{


//*****************************************************************************/
//   Rigorous computation   -  we use Krawczyk metod
//   to prove existence of zero of funtion F(x)
/*****************************************************************************/

template <typename MapType> template <typename FloatVector>
KrawczykResult Krawczyk<MapType>::proof (FloatVector &x,  double size,
                                         int maxNumberOfIterations)
{
   typedef  typename MapType::VectorType::ScalarType  ScalarType;
   typename MapType::VectorType X(dim),           // initial conditions
                                x0(dim);

   for(int i=0; i< dim; i++)
   {
       X[i]  = ScalarType(x[i]-size, x[i]+size);
       x0[i] = ScalarType(x[i]);
   }

   return proof(x0, X, maxNumberOfIterations);

}


template <typename MapType>
KrawczykResult Krawczyk<MapType>::proof (const typename MapType::VectorType &A_x0,
                                         const typename MapType::VectorType &A_X,
                                         int maxNumberOfIterations)
{

 x0 = A_x0;
 X = A_X;

 KrawczykResult exit_code = TooManyIterations;
 bool comp_F_x0 = true ;           // flag : true = computation of F(x_0) is needed

 for(numberOfIterations=1; numberOfIterations<maxNumberOfIterations; numberOfIterations++)  // iteration of taking intersection and Krawczyk metod
 {
    // Computation for a point x0
    if(comp_F_x0)
    {
       comp_F_x0 = false;

       typename MapType::MatrixType dF_x0(dim, dim);

       F_x0 = F(x0, dF_x0);

       // We take as matrix C for Krawczyk operator an inverse of Jacobi matrix at point x0
       C = midMatrix(capd::matrixAlgorithms::gaussInverseMatrix(midMatrix(dF_x0)));

       // We check if C is invertible. If it fails, an excepction will be thrown.
       capd::matrixAlgorithms::gaussInverseMatrix(C);

    }

    // computation for the set X
    dF_X = F[X];

    /*  KRAWCZYK OPERATOR   */
    K = x0 - C * F_x0 +(MapType::MatrixType::Identity(dim) - C * dF_X)*(X-x0);   //Krawczyk

    if( subsetInterior(K, X))
    {
        // K is subset of int X  - there exists exactly one zero of F in X
        exit_code = ZeroExists;
        break;
    }
    else
    {
       if(subset(X, K))
       {
           // K contains X - try to change parameters
         exit_code = ResultUndefined;
         break;
       }
       else
       {
          try
          {
            X=intersection(X, K);
            // X is partialy contained in K - we try to take intersection of X and K as new set X
            if( !subset(x0, X))
            {
                x0=midVector(X);
                comp_F_x0 = true;
            }
          }
          catch(std::runtime_error &e)
          {
             //Intersection of X and K is empty. There is no zeroes in set X";
             exit_code = NoZeroes;
             break;
          }
       }
    }
 }

 return exit_code;
}

/*********************************************************************************************/
// It computes Krawczyk Operator
/*********************************************************************************************/

template <typename MapType>
typename MapType::VectorType Krawczyk<MapType>::KrawczykOperator (
                                  const typename MapType::VectorType &A_x0,
                                  const typename MapType::VectorType &A_X)
{

  x0 = A_x0;
  X  = A_X;

  MatrixType dF_x0;              //  derivative of F computed in a point x0

  F_x0 = F(x0, dF_x0);

  // We take as matrix C for Krawczyk operator an inverse of the Jacobi matrix at the point x0
  C = midMatrix(capd::matrixAlgorithms::gaussInverseMatrix(midMatrix(dF_x0)));

  // We check if C is invertible. If it fails, an exception will be thrown.
  capd::matrixAlgorithms::gaussInverseMatrix(C);

  // Derivative of F on set X
  dF_X = F[X];

  /*  KRAWCZYK OPERATOR   */
  K = x0 - C * F_x0 +(MatrixType::Identity(dim) - C * dF_X)*(X-x0);

  return K;
}




template <typename MapType>
typename MapType::VectorType KrawczykOperator (const typename MapType::VectorType& x0,  
                                               const typename MapType::VectorType& X, 
                                               MapType &F)
{

  int dim = F.dimension();

  typename MapType::VectorType F_x0(dim);        //  function F computed at point x0

  typename MapType::MatrixType C(dim, dim),        // Matrix C for Krawczyk metod
                               dF_X(dim, dim),      //  derivative of F computed on set X
                               dF_x0;              //  derivative of F computed in a point x0

  F_x0 = F(x0, dF_x0);

  // We take as matrix C for Krawczyk operator an inverse of the Jacobi matrix at the point x0
  C = midMatrix(capd::matrixAlgorithms::gaussInverseMatrix(midMatrix(dF_x0)));

  // We check if C is invertible. If it fails, an exception will be thrown.
  capd::matrixAlgorithms::gaussInverseMatrix(C);

  // Derivative of F on set X
  dF_X = F[X];

  /*  KRAWCZYK OPERATOR   */

  typename MapType::VectorType K = x0 - C * F_x0 +(MapType::MatrixType::Identity(dim) - C * dF_X)*(X-x0);   //Krawczyk

  return K;
}



/*********************************************************************************************/

}} // end namespace capd::newton

#endif // _CAPD_NEWTON_KRAWCZYK_HPP_ 

/// @}
