/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file RowVector.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_VECTALG_ROWVECTOR_HPP_ 
#define _CAPD_VECTALG_ROWVECTOR_HPP_ 

#include <stdexcept>
#include "capd/vectalg/RowVector.h"
#include "capd/vectalg/Vector.hpp"

namespace capd{
namespace vectalg{

template<typename Scalar, int cols>
RowVector<Scalar,cols>::operator Vector<Scalar,cols>() const
{
  Vector<Scalar,cols> result(dimension(),true);
  const_iterator b=begin(), e=end();
  typename Vector<Scalar,cols>::iterator i=result.begin();
  while(b!=e)
  {
    *i = *b;
    ++i;
    ++b;
  }
  return result;
}


template<typename Scalar, int cols>
Vector<Scalar, cols> diam(const RowVector<Scalar, cols> & v)
{
   typedef typename RowVector<Scalar, cols>::ScalarType ScalarType;
   Vector<Scalar, cols> result(v.dimension());
   typename Vector<Scalar, cols>::iterator i=result.begin();
   typename RowVector<Scalar, cols>::const_iterator b=v.begin(), e=v.end();
   while(b!=e)
   {
      *i = (ScalarType(b->rightBound()) - ScalarType(b->leftBound())).rightBound();
      ++i;
      ++b;
   }
   return result;
}

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_ROWVECTOR_HPP_ 

/// @} 
