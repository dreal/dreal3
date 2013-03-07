/////////////////////////////////////////////////////////////////////////////
/// @file Interval_Friend.h
///
/// Interval Arithmetics - functions template declarations
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_INTERVAL_INTERVALFRIEND_H_ 
#define _CAPD_INTERVAL_INTERVALFRIEND_H_ 


//////////////////////////////////////////////////////////////////////////
//     access to interval ends
//////////////////////////////////////////////////////////////////////////

/// returns interval containing left end
template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd >  left( const Interval< T_Bound, T_Rnd >  & A_iv )
{
   return Interval<T_Bound, T_Rnd>( A_iv.leftBound());
}

/// returns interval containing right end
template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd >  right( const Interval< T_Bound, T_Rnd >  & A_iv )
{
   return Interval<T_Bound, T_Rnd>( A_iv.rightBound() );
}

/// returns left end
template < typename T_Bound, typename T_Rnd> 
inline T_Bound  leftBound( const Interval< T_Bound, T_Rnd >  & A_iv )
{
  return  A_iv.leftBound();
}

/// returns right end
template < typename T_Bound, typename T_Rnd> 
inline T_Bound  rightBound( const Interval< T_Bound, T_Rnd >  & A_iv )
{
  return  A_iv.rightBound();
}


//////////////////////////////////////////////////////////////////////////
//     RELATIONS
//////////////////////////////////////////////////////////////////////////

/// the relation  ==
template < typename T_Bound, typename T_Rnd> 
inline bool operator == (const Interval< T_Bound, T_Rnd > & A_iv1, 
                         const Interval< T_Bound, T_Rnd > & A_iv2)
{
   return ((A_iv1.leftBound()==A_iv2.leftBound()) && (A_iv1.rightBound()==A_iv2.rightBound()));
}

/// weak inequality relation <=
template < typename T_Bound, typename T_Rnd> 
inline bool operator <= (const Interval< T_Bound, T_Rnd > & A_iv1, 
                         const Interval< T_Bound, T_Rnd > & A_iv2)
{
   return (A_iv1.rightBound() <= A_iv2.leftBound());
}


/// weak inequality relation >=
template < typename T_Bound, typename T_Rnd> 
inline bool operator >= (const Interval< T_Bound, T_Rnd > & A_iv1, 
                         const Interval< T_Bound, T_Rnd > & A_iv2)
{
   return (A_iv1.leftBound()>= A_iv2.rightBound() );
}

/// strong inequality <
template < typename T_Bound, typename T_Rnd> 
inline bool operator < (const Interval< T_Bound, T_Rnd > & A_iv1, 
                        const Interval< T_Bound, T_Rnd > & A_iv2)
{
   return (A_iv1.rightBound() < A_iv2.leftBound());
}

/// strong inequality relation >
template < typename T_Bound, typename T_Rnd> 
inline bool operator > (const Interval< T_Bound, T_Rnd > & A_iv1, 
                        const Interval< T_Bound, T_Rnd > & A_iv2)
{
   return (A_iv1.leftBound()> A_iv2.rightBound());
}

/// the relation  !=  ( as a negation of  ==)
template < typename T_Bound, typename T_Rnd> 
inline bool operator != (const Interval< T_Bound, T_Rnd > & A_iv1, 
                         const Interval< T_Bound, T_Rnd > & A_iv2)
{
   return ((A_iv1.leftBound()!= A_iv2.leftBound()) || (A_iv1.rightBound() != A_iv2.rightBound()));
}


//////////////////////////////////////////////////////////////////////////
//     INPUT and OUTPUT
//////////////////////////////////////////////////////////////////////////

/// sending an Interval to a stream
template < typename T_Bound, typename T_Rnd> 
std::ostream & operator << (std::ostream & s, 
                            const Interval< T_Bound, T_Rnd > & A_iv);

/// reading an Interval from a stream
template < typename T_Bound, typename T_Rnd> 
std::istream & operator >> (std::istream & s, 
                            Interval< T_Bound, T_Rnd > & A_iv);

template < typename T_Bound, typename T_Rnd>
std::ostream & bitWrite(std::ostream & out, const Interval< T_Bound, T_Rnd > &iv);

template < typename T_Bound, typename T_Rnd>
std::istream & bitRead(std::istream & in, Interval< T_Bound, T_Rnd > &iv);

template < typename T_Bound, typename T_Rnd>
std::ostream & hexWrite(std::ostream & out, const Interval< T_Bound, T_Rnd > &iv);

template < typename T_Bound, typename T_Rnd>
std::istream & hexRead(std::istream & in, Interval< T_Bound, T_Rnd > &iv);

template < typename T_Bound, typename T_Rnd>
std::ostream & binWrite(std::ostream & out, const Interval< T_Bound, T_Rnd > &iv);

template < typename T_Bound, typename T_Rnd>
std::istream & binRead(std::istream & in, Interval< T_Bound, T_Rnd > &iv);
//////////////////////////////////////////////////////////////////////////
//     ARITHMETIC OPERATORS
//////////////////////////////////////////////////////////////////////////

/// unary operator -
template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator-(const Interval< T_Bound, T_Rnd> & A_iv)
{
  return(Interval< T_Bound, T_Rnd>(-A_iv.rightBound(),-A_iv.leftBound()));
}// unary operator -


template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> operator + (const Interval< T_Bound, T_Rnd>& A_iv1, 
                                      const Interval< T_Bound, T_Rnd>& A_iv2);

template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> operator - (const Interval< T_Bound, T_Rnd>& A_iv1, 
                                      const Interval< T_Bound, T_Rnd>& A_iv2);

template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> operator * (const Interval< T_Bound, T_Rnd>& A_iv1, 
                                      const Interval< T_Bound, T_Rnd>& A_iv2);

template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> operator / (const Interval< T_Bound, T_Rnd>& A_iv1, 
                                      const Interval< T_Bound, T_Rnd>& A_iv2);

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator ^ (const Interval< T_Bound, T_Rnd>& A_iv1, 
                                             int i)
{
   return power(A_iv1, i);
}


//////////////////////////////////////////////////////////////////////////
//     ARITHMETIC OPERATORS  between Interval and double
//////////////////////////////////////////////////////////////////////////
/*
template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator + (const Interval< T_Bound, T_Rnd> & A_iv, 
                                             double A_x)
{
  return A_iv + T_Bound(A_x); 
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator + (double A_x, 
                                             const Interval< T_Bound, T_Rnd> & A_iv)
{
  return A_iv + T_Bound(A_x); 
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator - (const Interval< T_Bound, T_Rnd> & A_iv, 
                                             double A_x)
{
  return A_iv - T_Bound(A_x); 
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator - (double A_x, 
                                             const Interval< T_Bound, T_Rnd> & A_iv)
{
  return T_Bound(A_x) - A_iv  ; 
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator * (const Interval< T_Bound, T_Rnd> & A_iv, 
                                             double A_x)
{
  return A_iv * T_Bound(A_x); 
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator * (double A_x, 
                                             const Interval< T_Bound, T_Rnd> & A_iv)
{
  return A_iv * T_Bound(A_x); 
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator / (const Interval< T_Bound, T_Rnd> & A_iv, 
                                             double A_x)
{
  return A_iv / T_Bound(A_x); 
}

template < typename T_Bound, typename T_Rnd> 
inline Interval< T_Bound, T_Rnd> operator / (double A_x, 
                                             const Interval< T_Bound, T_Rnd> & A_iv)
{
  return  T_Bound(A_x) / A_iv ; 
}

*/

//////////////////////////////////////////////////////////////////////////
// These functions are called by arithmetic operators 
//    Operators are defined inside class to provide implicite conversions  
//    and therefore are 'inline' functions.
//    Because of that we only call the following non 'inline' functions
//////////////////////////////////////////////////////////////////////////

/// Interval + BoundType
template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> add(const Interval< T_Bound, T_Rnd> & A_iv, 
                              const T_Bound &A_x);

/// Interval - BoundType
template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> substract(const Interval< T_Bound, T_Rnd> & A_iv, 
                                    const T_Bound &A_x);
  
/// BoundType - Interval 
template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> substract(const T_Bound  &A_x,
                                    const Interval< T_Bound, T_Rnd> & A_iv);

/// Interval * BoundType
template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> multiply(const Interval< T_Bound, T_Rnd>& A_iv, 
                                   const T_Bound& A_x);

/// Interval / BoundType
template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> divide(const Interval< T_Bound, T_Rnd>& A_iv, 
                                 const T_Bound& A_x);

///   BoundType / Interval 
template < typename T_Bound, typename T_Rnd> 
Interval< T_Bound, T_Rnd> divide(const T_Bound& A_x,
                                 const Interval< T_Bound, T_Rnd>& A_iv);



#endif // _CAPD_INTERVAL_INTERVALFRIEND_H_ 
