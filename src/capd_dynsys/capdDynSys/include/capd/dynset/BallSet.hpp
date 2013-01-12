
/////////////////////////////////////////////////////////////////////////////
/// @file BallSet.hpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_DYNSET_BALLSET_HPP_ 
#define _CAPD_DYNSET_BALLSET_HPP_ 

#include "capd/dynset/BallSet.h"
#include "capd/vectalg/Vector_Interval.hpp"

namespace capd{
namespace dynset{

template<typename MatrixType>
typename BallSet<MatrixType>::ScalarType BallSet<MatrixType>::size(void)
{
  return capd::vectalg::size(intervalBall(x,r));
}

template<typename MatrixType>
void BallSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType> &dynsys)
{
  VectorType y(x.dimension()), s(x.dimension());

/*   
  radius is multipled by the Lipschitz constant of the generator of DynSys
  on the interval enclosure of the ball. Note that the proper computation of Lipschitz
  for flows is hidden in the implementation of Lipschitz for flows (class odenum)
*/
  r *= dynsys.Lipschitz(intervalBall(x,r),*n);

/* x is replaced by the center of its image under the generator */
  y = dynsys.Phi(x) + dynsys.Remainder(x);
  split(y,s);
  x = y;
/* and the norm of the arising deviation s is added to the radius */
  r += (*n)(s);
  r = r.rightBound();
}

template<typename MatrixType>
void BallSet<MatrixType>::move(capd::dynsys::DynSys<MatrixType> &dynsys, BallSet &result) const
{
  VectorType y(x.dimension()),s(x.dimension());

/*   
  radius is multipled by the Lipschitz constant of the generator of DynSys
  on the IntervalType enclosure of the ball. Note that the proper computation of Lipschitz
  for flows is hidden in the implementation of Lipschitz for flows (class odenum)
*/
  result.r = r*dynsys.Lipschitz(intervalBall(x,r),*n);

/* x is replaced by the center of its image under the generator */
  y = dynsys.Phi(x) + dynsys.Remainder(x);
  split(y,s);
  result.x = y;
/* and the norm of the arising deviation s is added to the radius */
  result.r += (*n)(s);
  result.r = result.r.rightBound();
  result.n = n;
}

template<typename MatrixType>
std::string BallSet<MatrixType>::show(void) const
{
  std::ostringstream descriptor;
  descriptor << "BallSet(" << n->show() << "): x=";
  descriptor << x << " r=";
  descriptor << r << " ";
  return descriptor.str();
}

template<typename MatrixType>
typename BallSet<MatrixType>::VectorType BallSet<MatrixType>::affineTransformation(
    const MatrixType& A_M,
    const VectorType& A_C
  ) const
{
  return A_M*(intervalBall(x,r)-A_C);
}


}} // namespace capd::dynset

#endif // _CAPD_DYNSET_BALLSET_HPP_ 
