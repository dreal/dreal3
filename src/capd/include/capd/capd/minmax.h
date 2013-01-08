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

   template<typename T>
   inline T min(const T& x, const T& y)
   {
      return (x<y ? x : y);
   }

   template<typename T>
   inline T max(const T& x, const T& y)
   {
      return (x<y ? y : x);
   }

   template<typename T>
   inline T abs(const T& x)
   {
      return (x<0.) ? -x : x;
   }

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

#endif // _CAPD_CAPD_MINMAX_H_

/// @}
