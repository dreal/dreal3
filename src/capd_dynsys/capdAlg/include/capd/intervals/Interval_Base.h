/////////////////////////////////////////////////////////////////////////////
/// @file Interval_Base.h
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


#ifndef _CAPD_INTERVAL_INTERVALBASE_H_ 
#define _CAPD_INTERVAL_INTERVALBASE_H_ 

namespace capd{
namespace intervals{

//////////////////////////////////////////////////////////////////////////
//     constructors 
//////////////////////////////////////////////////////////////////////////


template < typename T_Bound, typename T_Rnd >
inline Interval<T_Bound, T_Rnd>::Interval()
#ifdef __INTERVAL_INIT_0__
                  : m_left(0.), m_right(0.)
#endif
{}

/// copying constructor
template < typename T_Bound, typename T_Rnd>
inline Interval < T_Bound, T_Rnd >::Interval( const Interval & A_iv )
               : m_left( A_iv.m_left ), m_right( A_iv.m_right )
{}

/// constructor from any class that can be coverted to BoundType
template < typename T_Bound, typename T_Rnd> 
//template < typename T_Scalar >
//inline Interval<T_Bound, T_Rnd>::Interval( const T_Scalar & A_scalar )
//     : m_left( T_Bound( A_scalar ) ), m_right( T_Bound( A_scalar ) )
inline Interval<T_Bound, T_Rnd>::Interval( const T_Bound & A_scalar )
//inline Interval<T_Bound, T_Rnd>::Interval( T_Bound A_scalar )
     : m_left( A_scalar ), m_right( A_scalar )
{}
///// constructor from any class that can be coverted to BoundType
//template < typename T_Bound, typename T_Rnd>
////template < typename T_Scalar >
////inline Interval<T_Bound, T_Rnd>::Interval( const T_Scalar & A_scalar )
////     : m_left( T_Bound( A_scalar ) ), m_right( T_Bound( A_scalar ) )
//inline Interval<T_Bound, T_Rnd>::Interval( const volatile T_Bound & A_scalar )
//     : m_left( A_scalar ), m_right( A_scalar )
//{}

template < typename T_Bound, typename T_Rnd>
inline Interval<T_Bound, T_Rnd>::Interval(const char left[], const char right[]){
  m_left = IntervalIOTraits<T_Bound>::readDown(left);
  m_right = IntervalIOTraits<T_Bound>::readUp(right);
  checkInterval("constructor ", m_left, m_right);
}
template < typename T_Bound, typename T_Rnd>
inline Interval<T_Bound, T_Rnd>::  Interval(const std::string & left, const std::string & right){
	m_left = IntervalIOTraits<T_Bound>::readDown(left);
	m_right = IntervalIOTraits<T_Bound>::readUp(right);
	checkInterval("constructor ", m_left, m_right);
}
/// constructor from any class that can be coverted to BoundType
template < typename T_Bound, typename T_Rnd>
//template < typename T_Scalar1, typename T_Scalar2 >
//Interval<T_Bound, T_Rnd>::Interval
//       ( const T_Scalar1 & A_left, const T_Scalar2 & A_right ) 
//       : m_left( T_Bound( A_left ) ), m_right( T_Bound( A_right ) )
Interval<T_Bound, T_Rnd>::Interval
        ( const T_Bound & A_left, const T_Bound & A_right ) 
        : m_left( A_left ), m_right( A_right )
{
   checkInterval("constructor ", m_left, m_right);
}

///// constructor from any class that can be coverted to BoundType
//template < typename T_Bound, typename T_Rnd>
////template < typename T_Scalar1, typename T_Scalar2 >
////Interval<T_Bound, T_Rnd>::Interval
////       ( const T_Scalar1 & A_left, const T_Scalar2 & A_right )
////       : m_left( T_Bound( A_left ) ), m_right( T_Bound( A_right ) )
//Interval<T_Bound, T_Rnd>::Interval
//        ( const volatile T_Bound & A_left, const volatile T_Bound & A_right )
//        : m_left( A_left ), m_right( A_right )
//{
//   checkInterval("constructor ", m_left, m_right);
//}

//////////////////////////////////////////////////////////////////////////
//     access to interval ends
//////////////////////////////////////////////////////////////////////////

template < typename T_Bound, typename T_Rnd> 
inline typename Interval<T_Bound, T_Rnd>::BoundReturnType Interval<T_Bound, T_Rnd>::leftBound() const
{
  return m_left;
}

template < typename T_Bound, typename T_Rnd> 
inline typename Interval<T_Bound, T_Rnd>::BoundReturnType Interval<T_Bound, T_Rnd>::rightBound() const
{
  return m_right;
}

template < typename T_Bound, typename T_Rnd> 
inline void Interval<T_Bound, T_Rnd>::setLeftBound(const T_Bound & A_left)
{
  m_left = A_left;
  checkInterval("setLeftBound ", m_left, m_right);
}

template < typename T_Bound, typename T_Rnd> 
inline void Interval<T_Bound, T_Rnd>::setRightBound(const T_Bound & A_right)
{
  m_right = A_right;
  checkInterval("setRightBound ", m_left, m_right);
}

template < typename T_Bound, typename T_Rnd> 
inline Interval<T_Bound, T_Rnd> Interval<T_Bound, T_Rnd>::left() const
{
  return Interval< T_Bound, T_Rnd > ( T_Bound(m_left) );
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd >  Interval<T_Bound, T_Rnd>::right() const
{
  return Interval<T_Bound, T_Rnd>( T_Bound(m_right) );
}


//////////////////////////////////////////////////////////////////////////
//        INCLUSIONS
//////////////////////////////////////////////////////////////////////////

template < typename T_Bound, typename T_Rnd> 
template < typename T_Scalar >
inline bool Interval<T_Bound, T_Rnd>::contains(const T_Scalar & A_x) const
{
   return (m_left <= (T_Bound)A_x) && ((T_Bound)A_x <= m_right);
}

template < typename T_Bound, typename T_Rnd> 
inline bool Interval<T_Bound, T_Rnd>::contains(const Interval<T_Bound, T_Rnd>& A_iv) const
{
  return (m_left <= A_iv.m_left) && (A_iv.m_right <= m_right);
}

template < typename T_Bound, typename T_Rnd> 
template < typename T_Scalar >
inline bool Interval<T_Bound, T_Rnd>::containsInInterior(const T_Scalar & A_x) const
{
   return (m_left < (T_Bound)A_x) && ((T_Bound)A_x < m_right);
}

template < typename T_Bound, typename T_Rnd> 
inline bool Interval<T_Bound, T_Rnd>::containsInInterior(const Interval<T_Bound, T_Rnd>& A_iv) const
{
  return (m_left < A_iv.m_left) && (A_iv.m_right < m_right);
}


template < typename T_Bound, typename T_Rnd> 
inline bool Interval<T_Bound, T_Rnd>::subset(const Interval<T_Bound, T_Rnd> & A_iv) const
{
  return (A_iv.m_left <= m_left) && ( m_right <= A_iv.m_right); 
}

template < typename T_Bound, typename T_Rnd> 
inline bool Interval<T_Bound, T_Rnd>::subsetInterior(const Interval<T_Bound, T_Rnd> & A_iv) const
{
  return (A_iv.m_left < m_left) && ( m_right < A_iv.m_right); 
}


//////////////////////////////////////////////////////////////////////////
//       mid, split, diam
//////////////////////////////////////////////////////////////////////////

// Midpoint of the interval
template < typename T_Bound, typename T_Rnd> 
inline Interval<T_Bound, T_Rnd> Interval<T_Bound, T_Rnd>::mid() const
{
  return Interval<T_Bound, T_Rnd> (( m_right + m_left ) / 2);       
}

// Splits interval into the form  mid + remainder, where mid - is middle point
template < typename T_Bound, typename T_Rnd> 
inline void Interval<T_Bound, T_Rnd>::split( Interval & A_rMid, 
                                             Interval & A_rRemainder ) const
{
  T_Rnd::roundUp();     
  T_Bound m = (m_right + m_left) /2,
          l = m - m_left,
          r = m_right - m;     
  A_rMid = Interval<T_Bound, T_Rnd>(m);
  A_rRemainder =  Interval<T_Bound, T_Rnd>( -l , r);        
} 

// Splits interval into the form  mid + remainder, where mid - is middle point
template < typename T_Bound, typename T_Rnd>
inline void Interval<T_Bound, T_Rnd>::split( T_Bound & A_rMid,
                                             Interval & A_rRemainder ) const
{
  T_Rnd::roundUp();
  A_rMid = (m_right + m_left) /2;
  T_Bound l = A_rMid - m_left,
          r = m_right - A_rMid;
  A_rRemainder =  Interval<T_Bound, T_Rnd>( -l , r);
}

//////////////////////////////////////////////////////////////////////////
//        CONSTANTS
//////////////////////////////////////////////////////////////////////////

template < typename T_Bound, typename T_Rnd> 
inline Interval<T_Bound, T_Rnd> Interval<T_Bound, T_Rnd>::pi()
{
  return Interval<T_Bound, T_Rnd>( 3.1415926535897932, 3.1415926535897934 );
}

template < typename T_Bound, typename T_Rnd> 
inline Interval<T_Bound, T_Rnd> Interval<T_Bound, T_Rnd>::euler()
{
   return Interval<T_Bound, T_Rnd>( 2.7182818284590452, 2.7182818284590454 );
}


}} // namespace capd::intervals 

#endif // _CAPD_INTERVAL_INTERVALBASE_H_ 
