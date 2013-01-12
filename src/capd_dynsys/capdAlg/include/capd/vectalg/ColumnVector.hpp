/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ColumnVector.hpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_VECTALG_COLUMNVECTOR_HPP_ 
#define _CAPD_VECTALG_COLUMNVECTOR_HPP_ 

#include <stdexcept>
#include "capd/vectalg/ColumnVector.h"
#include "capd/vectalg/Vector.hpp"

namespace capd{
namespace vectalg{

template<typename Scalar,int rows>
ColumnVector<Scalar,rows>::operator Vector<Scalar,rows>() const
{
  Vector<Scalar,rows> result(dimension(),true);
  const_iterator b=begin(), e=end();
  typename Vector<Scalar,rows>::iterator i=result.begin();
  while(b!=e)
  {
    *i = *b;
    ++i;
    ++b;
  }
  return result;
}

}} // namespace capd::vectalg

#endif // _CAPD_VECTALG_COLUMNVECTOR_HPP_ 

/// @}
