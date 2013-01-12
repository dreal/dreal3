//////////////////////////////////////////////////////////////////////////////
///
///  @file IntervalTraits.h
///  
///  @author kapela  @date   Sep 5, 2011
//////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2011 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_INTERVALS_INTERVALTRAITS_H_
#define _CAPD_INTERVALS_INTERVALTRAITS_H_

namespace capd {
namespace intervals {
/// @addtogroup intervals
/// @{


template <typename T_Bound>
class IntervalTraits{
public:
  typedef T_Bound BoundType;
  typedef BoundType BoundContainer;
  typedef const BoundType &  BoundReturnType;
  typedef BoundType & BoundRefType;
};

template <>
class IntervalTraits<double>{
public:
  typedef double BoundType;
  typedef volatile BoundType BoundContainer;
  typedef BoundType BoundReturnType;
  typedef BoundType & BoundRefType;
};

template <>
class IntervalTraits<float>{
public:
  typedef float BoundType;
  typedef volatile BoundType BoundContainer;
  typedef BoundType BoundReturnType;
  typedef BoundType & BoundRefType;
};

template <>
class IntervalTraits<long double>{
public:
  typedef long double BoundType;
  typedef volatile BoundType BoundContainer;
  typedef BoundType BoundReturnType;
  typedef BoundType & BoundRefType;
};


/// @} 
}} // end of namespace capd::intervals

#endif /* _CAPD_INTERVALS_INTERVALTRAITS_H_ */
