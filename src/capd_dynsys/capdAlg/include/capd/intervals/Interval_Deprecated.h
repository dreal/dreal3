/////////////////////////////////////////////////////////////////////////////
/// @file Interval_Deprecated.h
///
/// Interval Arithmetics package 
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _CAPD_INTERVAL_INTERVALDEPRECATED_H_ 
#define _CAPD_INTERVAL_INTERVALDEPRECATED_H_ 

#ifdef __INTERVAL_DEPRECATED__

namespace capd{
namespace intervals{

template < typename T_Bound, typename T_Rnd> 
inline int in(T_Bound _value, const Interval< T_Bound, T_Rnd >& iv)  // inclusion
{
  return iv.contains(_value);
}

template < typename T_Bound, typename T_Rnd> 
inline int in(T_Bound _value, const Interval< T_Bound, T_Rnd >& iv, int interior)  // inclusion
{
  if(interior)
    return iv.containsInInterior(_value);
  else
    return iv.contains(_value);
}

template < typename T_Bound, typename T_Rnd> 
inline int in(const Interval< T_Bound, T_Rnd >& small_iv ,const Interval< T_Bound, T_Rnd >& iv, int interior)// inclusion
{
  if(interior)
    return small_iv.subsetInterior(iv);
  else
    return small_iv.subset(iv);
}


template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd > Left(const Interval< T_Bound, T_Rnd > &iv)
{
  return iv.left();
}
template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd > Right(const Interval< T_Bound, T_Rnd > &iv)
{
  return iv.right();
}

inline double Left(double d)
{
   return d;
}

inline double Right(double d)
{
   return d;
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd > diameter(const Interval< T_Bound, T_Rnd > &iv)
{
  return diam(iv);
}

template < typename T_Bound, typename T_Rnd> 
inline void iSplit(Interval< T_Bound, T_Rnd > *iv, T_Bound *diam)
{
  split(*iv, *diam);
}

template < typename T_Bound, typename T_Rnd> 
inline int Degenerate(const Interval< T_Bound, T_Rnd > &iv)
{
   return iv.contains(0.0);
}

inline int Degenerate(double &r)
{
   return (r==0.0);
}

template < typename T_Bound, typename T_Rnd> 
inline double fabs(const Interval< T_Bound, T_Rnd > &iv)
{
   return capd::abs(iv).rightBound();
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> Ihull( const Interval< T_Bound, T_Rnd> & i1, 
                                        const Interval< T_Bound, T_Rnd> & i2)
{
   return intervalHull(i1, i2);
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> solve_affine_inclusion(
                                                 const Interval< T_Bound, T_Rnd> & a, 
                                                 const Interval< T_Bound, T_Rnd> & p, 
                                                 const Interval< T_Bound, T_Rnd> & c)
{
   return solveAffineInclusion(a, p, c);
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> solve_affine_inclusion(
                                                 const Interval< T_Bound, T_Rnd> & a, 
                                                 const Interval< T_Bound, T_Rnd> & p, 
                                                 const Interval< T_Bound, T_Rnd> & c,
                                                 int & dir)
{
   return solveAffineInclusion(a, p, c, dir);
}

}} // namespace capd::intervals 


#endif // __INTERVAL_DEPRECATED__

#endif // _CAPD_INTERVAL_INTERVALDEPRECATED_H_ 

