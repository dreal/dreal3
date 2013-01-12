/////////////////////////////////////////////////////////////////////////////
/// @file Krawczyk.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _CAPD_NEWTON_KRAWCZYK_H_ 
#define _CAPD_NEWTON_KRAWCZYK_H_ 

#include <string>
#include <sstream>
#include "capd/newton/NewtonResult.h"

namespace capd{
namespace newton{


template <typename MapType>
class Krawczyk
{
  public:
     typedef typename MapType::VectorType VectorType;
     typedef typename MapType::MatrixType MatrixType;

     Krawczyk(MapType &A_F);

     template <typename FloatVector>
     KrawczykResult proof (FloatVector &x,  double size, int maxNumberOfIterations = 8);

     KrawczykResult proof (const VectorType &A_x0,
                           const VectorType &X,
                           int maxNumberOfIterations = 8);

     VectorType  KrawczykOperator(const VectorType &A_x0,
                                           const VectorType &A_X);

     int dim;
     int numberOfIterations;

     VectorType x0,
                X,
                F_x0,        //  function F computed at point x0
                K;           // value of Krawczyk operator

     MatrixType C,        // Matrix C for Krawczyk metod
                dF_X;      //  derivative of F computed on set X

     MapType &F;

  private:

     //bool log;

     //std::ostream stream;

};

template <typename MapType>
Krawczyk<MapType>::Krawczyk(MapType &A_F) : dim(A_F.dimension()), F(A_F)
{

}


//*****************************************************************************/
//   KrawczykProof  - Rigorous computation   -  we use Krawczyk metod
//   to prove existence of zero of funtion F(x)
//
//   INPUT:
//     x    - approximated zero of F,
//         size - radius of set X,  ( X = x + [-size, size]^n )
//     or  X    - set X
//     F    - class which can calculate value of the function F and its derivative dF
//
//
//   We compute Krawczyk operator
//      K = x - C*F(x) + (Id - C*dF(X))(X-x0)
//
//        C is a nonsingular matrix close to dF(x)^-1.
//
//   OUTPUT :
//     returns NewtonResult constant:
//
//     zeroExists = 1         - zero exists (K is subset of int X),
//     noZeroes = 0           - there is no zeros in the set X (intersection of K and X is empty),
//     tooManyIterations = -1 - we can still take intersection of X and K,
//                              but we exceed maximal number of iteration
//     undefined = -2         - X is subset of K,
//
/*****************************************************************************/
template <typename FloatVector, typename MapType>
KrawczykResult KrawczykProof (const FloatVector &x,  
                              double size,  
                              MapType &F)
{
   Krawczyk<MapType> krawczyk(F);
   return krawczyk.proof(x, size);
}


template <typename MapType>
KrawczykResult KrawczykProof ( const typename MapType::VectorType& x0, 
                               const typename MapType::VectorType& X,
                               MapType &F)
{
   Krawczyk<MapType> krawczyk(F);
   return krawczyk.proof(x0, X);
}


/**************************************************************************************/
//   Computes Krawczyk operator
//
//   INPUT:
//     x    - approximated zero of F,
//     X    - set X
//     F    - class which can calculate value of the function F and its derivative dF
//
//   OUTPUT:
//      K = x - C*F(x) + (Id - C*dF(X))(X-x0)
//
/*************************************************************************************/

template <typename MapType>
typename MapType::VectorType KrawczykOperator (const typename MapType::VectorType& x0,  
                                               const typename MapType::VectorType& X, 
                                               MapType &F);





}}  //end of namespace capd::newton

#include "capd/newton/Krawczyk.hpp"

#endif // _CAPD_NEWTON_KRAWCZYK_H_ 
