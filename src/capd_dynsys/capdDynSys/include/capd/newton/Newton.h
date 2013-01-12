/////////////////////////////////////////////////////////////////////////////
/// @file Newton.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _CAPD_NEWTON_NEWTON_H_ 
#define _CAPD_NEWTON_NEWTON_H_ 

#include <string>
#include <sstream>
#include "capd/newton/NewtonResult.h"

namespace capd{
namespace newton{

/////////////////////////////////////////////////////////////////////////////////
///
/// Default function for writing details on Newton Proof.
/// You can define your own specification  to replace this default function
/////////////////////////////////////////////////////////////////////////////////

template <typename IntervalVector, typename IntervalMatrix>
inline void  NewtonInfo(int iter,   IntervalVector x0,   IntervalVector X,
                          IntervalVector F_x0,  IntervalMatrix dF_X,  IntervalVector K)
{

}

//*****************************************************************************/
// NewtonProof
///
///  Rigorous existence proof of a zero of a given function F
///   
///  We compute rigorously Newton operator \f$ N = x - (dF(X)^-1) F(x) \f$
///  and we check assumptions of the Interval Newton Method.
///
///   @param[in]  x      approximated zero of F,
///   @param[in]  size   radius of set X,  ( \f$X = x + [-size, size]^n \f$ )
///   @param[in]  F      class which can calculate value of the function F (by calling F(x)) 
///                      and its derivative dF (by calling F[x])
///
///  @returns    NewtonResult constant:
///     zeroExists = 1         - zero exists (K is subset of X),
///     noZeroes = 0           - there is no zeros in the set X (intersection of K and X is empty),
///     tooManyIterations = -1 - we can still take intersection of X and K, but we exceed maximal number of iteration
///     undefined = -2         - X is subset of K,
///
/*****************************************************************************/

template <typename FloatVector, typename MapType>
NewtonResult NewtonProof ( FloatVector &x,  
                           double size,  
			                     MapType &F) ;


//*****************************************************************************/
// NewtonProof
///
///  Rigorous existence proof of a zero of a given function F
///   
///  We compute rigorously Newton operator \f$ N = x - (dF(X)^-1) F(x) \f$
///  and we check assumptions of the Interval Newton Method.
///
///   @param[in]  x      approximated zero of F, we assume that \f$ x \in X \f$
///   @param[in]  X      set X, in which we search for a zero of F
///   @param[in]  F      class which can calculate value of the function F and its derivative dF
///
///  @returns    NewtonResult constant:
///     zeroExists = 1         - zero exists (K is subset of X),
///     noZeroes = 0           - there is no zeros in the set X (intersection of K and X is empty),
///     tooManyIterations = -1 - we can still take intersection of X and K, but we exceed maximal number of iteration
///     undefined = -2         - X is subset of K,
///
/*****************************************************************************/
template <typename MapType>
NewtonResult NewtonProof ( const typename MapType::VectorType& x0, 
                           const typename MapType::VectorType& X,
                           MapType &F);


///////////////////////////////////////////////////////////////////////////////////////
//  NewtonOperator
///
///   Computes Newton operator
///
///   @param[in]    x    approximated zero of F, we assume that \f$ x \in X \f$
///   @param[in]    X    set X
///   @param[in]    F    class which can calculate value of the function F (by calling F(x)) 
///                      and its derivative dF (by calling F[x])
///
///   @returns    N = x - (dF(X)^-1)*F(x)
///
///////////////////////////////////////////////////////////////////////////////////////

template <typename MapType>
typename MapType::VectorType NewtonOperator ( const typename MapType::VectorType& x0,  
                                              const typename MapType::VectorType& X, 
					      MapType &F);

}}  //end of namespace capd::newton

#include "capd/newton/Newton.hpp"

#endif // _CAPD_NEWTON_NEWTON_H_ 
