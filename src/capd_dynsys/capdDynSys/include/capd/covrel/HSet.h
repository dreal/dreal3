

/////////////////////////////////////////////////////////////////////////////
/// @file HSet.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_COVREL_HSET_H_
#define _CAPD_COVREL_HSET_H_

#include <vector>
#include "capd/covrel/GridSet.h"

namespace capd{
/// Covering relations, H-sets, cones conditions
namespace covrel{
/// @addtogroup covrel
/// @{

enum Side { leftSide = -1, bothSides = 0, rightSide = 1};


/**
   this is an abstract class for h-sets - from paper by Gidea-Zgliczynski
   'Covering relations ...'  http://www.im.uj.edu.pl/~zgliczyn
*/
template <typename VectorT, typename IVectorT>
class HSet{
public:
  typedef VectorT VectorType;
  typedef IVectorT IVectorType;


  // @name  nonrigorous methods
  // nonrigorous computations - used usually in tests and setting up parameters
  // @{
  virtual bool outside(const VectorType &) const = 0; // verifies if a vector does not intersect support of h-set
  virtual bool inside (const VectorType &) const = 0; // verifies if a vector is inside the support of h-set
  virtual bool across (const VectorType &) const = 0; // verifies if a vector does not intersect N^+
  virtual bool mapaway(const VectorType &) const = 0; // verifies if the projection onto stable directions
                                                         // of a vector is outside the unit ball in a proper
                                                         // coordinate system
  // @}

  // @name rigorous methods:
  // @{
  virtual bool outside(const IVectorType & set) const = 0; ///< verifies if \c set does not intersect the support of h-set
  virtual bool inside (const IVectorType & set) const = 0; ///< verifies if \c set is inside the support of h-set,
  virtual bool across (const IVectorType & set) const = 0; ///< verifies if \c set does not intersect N^+
  virtual bool mapaway(const IVectorType & set) const = 0; ///< ???
  // @}

   virtual ~HSet(){}
}; //the end of abstract class HSet

/// verifies if \c set does not intersect the support of h-set
template <typename HSetType, typename SetType>
inline bool outside(const HSetType & hset, const SetType & set){
	return hset.outside(set);
}

/// verifies if \c set is inside the support of h-set
template <typename HSetType, typename SetType>
inline bool inside(const HSetType & hset, const SetType & set){
	return hset.outside(set);
}

/// verifies if \c set does not intersect N^+
template <typename HSetType, typename SetType>
inline bool across(const HSetType & hset, const SetType & set){
	return hset.across(set);
}

///
template <typename HSetType, typename SetType>
inline bool mapaway(const HSetType & hset, const SetType & set){
	return hset.mapaway(set);
}
/// Checks if \c set in on the left side of the \c hset (works only in 2D)
template <typename HSetType, typename SetType>
inline bool onLeft(const HSetType & hset, const SetType & set){
	return hset.onLeft(set);
}
/// Checks if \c set in on the right side of the \c hset (works only in 2D)
template <typename HSetType, typename SetType>
inline bool onRight(const HSetType & hset, const SetType & set){
	return hset.onRight(set);
}

/// @}
}} // namespace capd::covrel

#endif // _CAPD_COVREL_HSET_H_
