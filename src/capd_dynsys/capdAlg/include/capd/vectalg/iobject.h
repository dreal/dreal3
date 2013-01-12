/// @addtogroup vectalg
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file iobject.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_VECTALG_IOBJECT_H_
#define _CAPD_VECTALG_IOBJECT_H_

namespace capd{
namespace vectalg{

/**
 *  splits source object given by [sourceBegin, sourceEnd]
 *  into  form center + diameter  where diameter = [-radius,radius] on each coordinatedimension
 *  @param[in]    sourceBegin,sourceEnd        object to be splitted,
 *  @param[out]   center        returns center of the object (it should be iterator on first element)
 *  @param[out]   diameter      returns zero centered set [-radius,radius] (it should be iterator on first element)
 */

template<typename SourceIterator, typename Iterator1, typename Iterator2>
void split(const SourceIterator sourceBegin, const SourceIterator sourceEnd,
           Iterator1 center, Iterator2  diameter);
/**
 *  splits IntervalObject v into  form center + [-radius, radius] form
 *  @param[in,out]  v   object to be splitted, returns center of the object.
 *  @param[out]     rv  returns zero centered set [-radius, radius].
 */

template<typename IntervalObject1, typename IntervalObject2>
inline
void split(IntervalObject1& v, IntervalObject2& rv)
{
  if(v.dimension()!=rv.dimension())
    throw std::range_error("Unequal dimensions in function capd::vectalg::split");
  split(v.begin(),v.end(),v.begin(),rv.begin());
}


/**
 *  splits IntervalObject v into  form center + diameter  where diameter = [-radius,radius] on each coordinate
 *  @param[in]    v        object to be splitted,
 *  @param[out]   center   returns center of the object.
 *  @param[out]   diameter   returns zero centered set [-radius,radius].
 */
template<typename IntervalObject, typename CenterType>
inline
void split(const IntervalObject & v, CenterType& center, IntervalObject & diameter) {
  if((v.dimension()!=center.dimension()) && (v.dimension()!=diameter.dimension()))
    throw std::range_error("Unequal dimensions in function capd::vectalg::split");
  split(v.begin(),v.end(),center.begin(),diameter.begin());
}


/**
 *  returns the biggest diameter of IntervalObject (vector or matrix) coordinates
 */
template<typename IntervalObject>
typename IntervalObject::ScalarType size(const IntervalObject& v);

/**
 *  checks if IntervalObject v contains zero on all coordinates
 */

template<typename IntervalObject>
bool containsZero(const IntervalObject& v);

/**
 *  checks if IntervalObject v1 is contained in IntervalObject v2
 */

template<typename IntervalObject>
bool subset(const IntervalObject& v1, const IntervalObject& v2);

/**
 * checks if IntervalObject v1 is contained in interior of IntervalObject v2
 */

template<typename IntervalObject>
bool subsetInterior(const IntervalObject& v1, const IntervalObject& v2);

/// //////////////////////////////////////////////////////////////////////////////
// intersection
///
/// intersection of two interval objects (vectors, matrices)
/// @returns
///   true and intersection in result if intersection is not empty
///   false if intersection is empty (value of result is meaningless)
///
/// //////////////////////////////////////////////////////////////////////////////

template<typename Iterator1, typename Iterator2, typename ResultIterator>
bool intersection(Iterator1 b1, Iterator2 b2, ResultIterator b, ResultIterator e);

/// //////////////////////////////////////////////////////////////////////////////
// intersection
///
/// intersection of two interval objects (vectors, matrices)
/// @returns
///   true and intersection in result if intersection is not empty
///   false if intersection is empty (value of result is meaningless)
///
/// //////////////////////////////////////////////////////////////////////////////

template<typename IntervalObject1, typename IntervalObject2, typename IntervalObject3>
inline
bool intersection(const IntervalObject1 &v1, const IntervalObject2 &v2, IntervalObject3 &result)
{
  if(v1.dimension()!=v2.dimension())
    throw std::range_error("Unequal dimensions in function capd::vectalg::intersection");
  if(v1.dimension()!=result.dimension())
    throw std::range_error("Unequal dimensions in function capd::vectalg::intersection");

  return intersection(v1.begin(),v2.begin(),result.begin(),result.end());
}

/// //////////////////////////////////////////////////////////////////////////////
// intersectionIsEmpty
///
/// checks if intersection of two interval vectors is empty
///
/// @returns
///   true  if intersection is empty
///   false if intersection is not empty
///
/// //////////////////////////////////////////////////////////////////////////////
template <typename Iterator1, typename Iterator2>
bool intersectionIsEmpty(Iterator1 b, Iterator1 e, Iterator2 b1);

/// //////////////////////////////////////////////////////////////////////////////
// intersectionIsEmpty
///
/// checks if intersection of two interval vectors is empty
///
/// @returns
///   true  if intersection is empty
///   false if intersection is not empty
///
/// //////////////////////////////////////////////////////////////////////////////
template <typename IntervalObject1, typename IntervalObject2>
inline
bool intersectionIsEmpty(const IntervalObject1 & v, const IntervalObject2 &w)
{
  return intersectionIsEmpty(v.begin(),v.end(),w.begin());
}


template<typename IntervalObject>
void intervalHull(const IntervalObject &v1, const IntervalObject &v2, IntervalObject &result);

template<typename IntervalObject, typename ResultContainer>
void diameter(const IntervalObject &v, ResultContainer &result);

template<typename IntervalObject, typename ResultType>
void mid(const IntervalObject& v, ResultType& result);

template<typename ResultType, typename IntervalObject>
ResultType midObject(const IntervalObject &v);

template<typename ResultType, typename IntervalObject>
void leftObject(const IntervalObject &v, ResultType& result);

template<typename ResultType, typename IntervalObject>
inline
ResultType leftObject(const IntervalObject &v)
{
  ResultType result(v.dimension());
  leftObject(v,result);
  return result;
}


template<typename ResultType, typename IntervalObject>
void rightObject(const IntervalObject &v, ResultType& result);

template<typename ResultType, typename IntervalObject>
inline
ResultType rightObject(const IntervalObject &v)
{
  ResultType result(v.dimension());
  rightObject(v,result);
  return result;
}

template <typename ResultType, typename ScalarType>
ResultType convertScalar(const ScalarType &v);

template<typename ResultType, typename ContainerType>
ResultType convertObject(const ContainerType &v);

template<typename VectorType>
VectorType conjVector(const VectorType & v);

}} // namespace capd::vectalg



#endif /* _CAPD_VECTALG_IOBJECT_H_ */
