//////////////////////////////////////////////////////////////////////////////
///
///  @file RoundingTraits.h
///  
///  @author kapela  @date   Apr 17, 2011
//////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2011 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_ROUNDING_ROUNDINGTRAITS_H_
#define _CAPD_ROUNDING_ROUNDINGTRAITS_H_

#include "capd/rounding/DoubleRounding.h"
#include "capd/rounding/IntRounding.h"

namespace capd {
namespace rounding {

//////////////////////////////////////////////////////////////////////////////
//   RoundingTraits
///
///  Class that for given type defines default class for rounding switching
///
//////////////////////////////////////////////////////////////////////////////

template <typename T>
class RoundingTraits {
public:
  typedef T RoundingType;
};

template <>
class RoundingTraits<double> {
public:
  typedef capd::rounding::DoubleRounding RoundingType;
};
template <>
class RoundingTraits<float> {
public:
  typedef capd::rounding::DoubleRounding RoundingType;
};
template <>
class RoundingTraits<long double> {
public:
  typedef capd::rounding::DoubleRounding RoundingType;
};

template <>
class RoundingTraits<int> {
public:
  typedef capd::rounding::IntRounding RoundingType;
};

template <typename T>
void setRounding(const capd::rounding::RoundingMode & rounding){
  switch(rounding){
    case capd::rounding::RoundCut:
      RoundingTraits<T>::RoundingType::roundCut();
      break;
    case capd::rounding::RoundDown:
      RoundingTraits<T>::RoundingType::roundDown();
      break;
    case capd::rounding::RoundUp:
      RoundingTraits<T>::RoundingType::roundUp();
      break;
    case capd::rounding::RoundNearest:
      RoundingTraits<T>::RoundingType::roundNearest();
      break;
    default:
      ;
  }
}

}} // end of namespace capd::rounding

#endif /* _CAPD_ROUNDING_ROUNDINGTRAITS_H_ */
