/// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file minmax.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/* min, max and abs definitions */

#ifndef _CAPD_CAPD_MINMAX_H_
#define _CAPD_CAPD_MINMAX_H_

#undef max
#undef min

namespace capd{

//
// The following lines was prone to errors
//
//template<typename T>
//inline T min(const T& x, const T& y) {
//  return (x<y ? x : y);
//}
//
//template<typename T>
//inline T max(const T& x, const T& y) {
//  return (x<y ? y : x);
//}


template<typename T>
inline T min(const T& x, const T & y) {
  return T::Specialization_of_min_function_not_defined();
}

template<>
inline long double min(const long double & x, const long double & y) {
  return (x<y ? x : y);
}

template<>
inline double min(const double & x, const double & y) {
  return (x<y ? x : y);
}

template<>
inline int min(const int & x, const int & y) {
  return (x<y ? x : y);
}



template<typename T>
inline T max(const T& x, const T & y) {
  return T::Specialization_of_max_function_not_defined();
}

template<>
inline long double max(const long double & x, const long double & y) {
  return (x<y ? y : x);
}

template<>
inline double max(const double & x, const double & y) {
  return (x<y ? y : x);
}

template<>
inline int max(const int & x, const int & y) {
  return (x<y ? y : x);
}

template<typename T>
inline T abs(const T& x) {
  return T::Specialization_of_abs_function_not_defined();
}

template<>
inline long double abs(const long double & x) {
  return (x<0.) ? -x : x;
}

template<>
inline double abs(const double & x) {
  return (x<0.) ? -x : x;
}

template<>
inline int abs(const int & x) {
  return (x<0.) ? -x : x;
}

} // end of namespace capd

// TODO : this can not be removed:
// Due to the problem with partial specializations these declarations needs to follow directly templates

namespace capd{
namespace intervals{
template < typename T_Bound, typename T_Rnd >
class Interval;
}  //namespace intervals

   // definitions in interval.h and interval.cpp
   template < typename T_Bound, typename T_Rnd>
   intervals::Interval< T_Bound, T_Rnd > min(const intervals::Interval< T_Bound, T_Rnd >& x, const intervals::Interval< T_Bound, T_Rnd >& y);
   template < typename T_Bound, typename T_Rnd>
   intervals::Interval< T_Bound, T_Rnd > max(const intervals::Interval< T_Bound, T_Rnd >& x, const intervals::Interval< T_Bound, T_Rnd >& y);
   template < typename T_Bound, typename T_Rnd>
   intervals::Interval< T_Bound, T_Rnd >  abs(const intervals::Interval< T_Bound, T_Rnd >& x);

} // namespace capd

#ifdef  __USE_FILIB__

#include <interval/interval.hpp>

namespace capd{
namespace filib{

template <typename T, ::filib::rounding_strategy R, ::filib::interval_mode M>
class Interval;

} // end of namespace filib

// definitions in capdAlg/capd/filib/Interval.h
template <typename T, ::filib::rounding_strategy R, ::filib::interval_mode M>
filib::Interval<T, R, M> abs (const filib::Interval<T, R, M> & A_inter);
template <typename T, ::filib::rounding_strategy R, ::filib::interval_mode M>
inline filib::Interval<T, R, M> max(const filib::Interval<T, R, M>& A_iv1, const filib::Interval<T, R, M>& A_iv2);
template <typename T, ::filib::rounding_strategy R, ::filib::interval_mode M>
inline filib::Interval<T, R, M> min (const filib::Interval<T, R, M>& A_iv1, const filib::Interval<T, R, M>& A_iv2);

} // namespace capd
#endif // __USE_FILIB__



#endif // _CAPD_CAPD_MINMAX_H_

/// @}
