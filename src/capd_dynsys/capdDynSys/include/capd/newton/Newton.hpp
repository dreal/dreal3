/////////////////////////////////////////////////////////////////////////////
/// @file Newton.hpp
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_NEWTON_NEWTON_HPP_ 
#define _CAPD_NEWTON_NEWTON_HPP_ 

#include <stdexcept>

#include "capd/newton/Newton.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"
namespace capd{
namespace newton{


/*****************************************************************************/
//   Rigorous existence proof of a zero of a given function F
/*****************************************************************************/

template <typename FloatVector, typename MapType>
NewtonResult NewtonProof (const FloatVector &x,  
                          double size,
			                    MapType &F)
{
   int dim = F.dimension();

   typename MapType::VectorType X(dim),           // initial conditions
                                x0(dim);

   typedef typename MapType::VectorType::ScalarType  ScalarType;

   for(int i=0; i< dim; i++)
   {
       X[i] = ScalarType(x[i]-size, x[i]+size);
       x0[i] = ScalarType(x[i]);
   }

   return NewtonProof(x0, X, F);

}


template <typename MapType>
NewtonResult NewtonProof ( const typename MapType::VectorType& x0, 
                           const typename MapType::VectorType& X,
                           MapType &F)
{

  int dim = F.dimension();

  typename MapType::VectorType F_x0(dim),        //  function F computed at point x0
                              N(dim);           // value of Newton operator

  typename MapType::MatrixType dF_X(dim, dim);      //  derivative of F computed on set X


  NewtonResult exit_code = TooManyIterations;
  bool comp_F_x0 = true ;           // flag : true = computation of F(x_0) is needed
  int iter = 0;

  for(iter=1; iter<8; iter++)  // iteration of taking intersection and Newton metod
  {
    // Computation for a point x0
    if(comp_F_x0)
    {
       comp_F_x0 = false;
       F_x0 = F(x0);
    }

    // computation for the set X
    dF_X = F[X];

    /* NEWTON OPERATOR   */
    // to compute A^{-1}*b  we solve A*x = b by gauss elimination
    // N = x0 -  capd::matrixAlgorithms::gaussInverseMatrix(dF_X) * F_x0;
    N = x0 -  capd::matrixAlgorithms::gauss(dF_X, F_x0);

    if( subset(N, X))
    {
        // N is subset of  X  - there exists exactly one zero of F in X
        exit_code = ZeroExists;
        break;
    }
    else
    {
       if(subset(X, N))
       {
           // N contains X - try to change parameters
         exit_code = ResultUndefined;
         break;
       }
       else
       {
          try
          {
            X=intersection(X, N);
            // X is partialy contained in N - we try to take intersection of X and N as new set X
            if( !subset(x0, X))
            {
                x0=midVector(X);
                comp_F_x0=1;
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

 NewtonInfo(iter, x0, X, F_x0, dF_X, N);

 return exit_code;
}


/*********************************************************************************************/
// It computes Newton Operator
/*********************************************************************************************/


template <typename MapType>
typename MapType::VectorType NewtonOperator (const typename MapType::VectorType& x0,  
                                             const typename MapType::VectorType& X, 
                                             MapType &F)
{
  typename MapType::VectorType F_x0  = F(x0);        //  function F computed at point x0

  typename MapType::MatrixType dF_X = F[X];          //  derivative of F computed on set X

  // NEWTON OPERATOR   
  typename MapType::VectorType N = x0 - capd::matrixAlgorithms::gauss(dF_X, F_x0);

  return N;
}


/*********************************************************************************************/

}} // end namespace capd::newton

#endif // _CAPD_NEWTON_NEWTON_HPP_ 
