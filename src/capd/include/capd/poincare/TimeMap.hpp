/// @addtogroup poincare
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file TimeMap.hpp
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file is part of the CAPD library.  This library is free software;
// you can redistribute it and/or modify it under the terms of the GNU
// General Public License as published by the Free Software Foundation;
// either version 2 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this software; see the file "license.txt".  If not, write to the
// Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.

#ifndef _CAPD_POINCARE_TIME_MAP_HPP_
#define _CAPD_POINCARE_TIME_MAP_HPP_

#include "capd/poincare/TimeMap.h"
#include "capd/map/C1Coeff.h"

namespace capd{
namespace poincare{



template <typename DS>
typename TimeMap<DS>::VectorType TimeMap<DS>::operator()(ScalarType Time, VectorType v)
// the point on trajectory just after time 'time'
{
   this->moveSet(Time, v);
   return v;
}

template <typename DS>
typename TimeMap<DS>::VectorType
TimeMap<DS>::operator()(ScalarType Time, VectorType v, MatrixType &der)
// the point on trajectory just after time 'time'
{
  capd::map::C1Coeff<MatrixType> coeffs(v, MatrixType::Identity(m_dim));
  this->moveSet(Time, coeffs);
  der = (MatrixType)coeffs;
  return (VectorType)coeffs;
}

}} // namespace capd::poincare


#endif // #define _CAPD_POINCARE_TIME_MAP_HPP_

/// @}
