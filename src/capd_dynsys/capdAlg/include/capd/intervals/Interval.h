/////////////////////////////////////////////////////////////////////////////
/// @file intervals/Interval.h
///
/// Interval Arithmetics Interface
///
/// @remark include this file if you link your program with capd library
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_INTERVAL_INTERVALINTF_H_
#define _CAPD_INTERVAL_INTERVALINTF_H_

#include <iostream>
#include "capd/auxil/minmax.h"
#include "capd/intervals/IntervalSettings.h"
#include "capd/intervals/IntervalError.h"
#include "capd/basicalg/TypeTraits.h"
#include "capd/rounding/RoundingTraits.h"
#include "capd/intervals/IntervalTraits.h"
#include "capd/basicalg/doubleFun.h"


namespace capd{
/// Interval arithmetics
namespace intervals{

/// @addtogroup intervals
/// @{


//template class IntervalTraits<double>;

template < typename T_Bound, typename T_Rnd = typename capd::rounding::RoundingTraits<T_Bound>::RoundingType >
class Interval;

//=================================================
// friend functions and friend operators
#include "capd/intervals/Interval_Friend.h"
//=================================================

//////////////////////////////////////////////////////////////////////////////
//   Interval
///
///  Definition of template class Interval
///
///  Template has two parameters:
///  - T_Bound - type of interval ends,
///  - T_Rnd - class that switches rounding (by default it is equal to T_Bound) .
///
///  T_Rnd has to provide methods that switch rounding mode:
///  - roundUp,
///  - roundDown,
///  - roundNearest.
///
///  To provide full functionality of the class Interval and related functions
///  class T_Bound has to provide methods:
///  - constructors: from double, int.
///  - relations ==  !=   <   <=   >   >=
///  - operators  + - * /  -(unary)
///  - operator =
///  - input, output operators <<  >>
///  - log, sqrt.
///  - capd::max, capd::min, capd::abs (to distinguish from standard template function)
///
///  @remark We do not assume that elementary function such sin, cos, tan, exp,...
///   for BoundType are computed correctly and therefore we do not use them
///   in interval version.
///   If you have type of endpoint which guarantee correctness of up and down rounding
///   you can write your own specialization of elementary functions e.g. taking advantage
///   of monocity.
///
///   @author Tomasz Kapela   @date 11-01-2006
//////////////////////////////////////////////////////////////////////////////

template < typename T_Bound, typename T_Rnd >
class Interval{

public:

  typedef T_Bound BoundType;
  typedef T_Rnd   RoundingPolicy;
  typedef typename IntervalTraits<BoundType>::BoundContainer BoundContainer;
  typedef typename IntervalTraits<BoundType>::BoundReturnType BoundReturnType;

  //======== definitions in intervalBase.h ==========================

  Interval();

  /// copying constructor
  Interval  ( const Interval & A_iv ) ;

  /// constructor from any class that can be coverted to BoundType
  // template < typename T_Scalar >
  // Interval( const T_Scalar & A_scalar );
  Interval(const BoundType & A_scalar);
  //Interval(BoundType A_scalar);

  //Interval(const volatile BoundType & A_scalar);
  
  /// constructor from any class that can be coverted to BoundType
  //template < typename T_Scalar1, typename T_Scalar2 >
  //Interval( const T_Scalar1 & A_left, const T_Scalar2 & A_right );
  Interval( const BoundType & A_left, const BoundType & A_right );
	//Interval( const volatile BoundType & A_left, const volatile BoundType & A_right );

  Interval(const char left[], const char right[]);

  Interval(const std::string & left, const std::string & right);

  BoundReturnType leftBound() const;  ///<  returns the left end of the interval
  BoundReturnType rightBound() const; ///<  returns the right end of the interval

  void setLeftBound(const T_Bound & A_left);
  void setRightBound(const T_Bound & A_right);

  Interval left() const;      ///< returns interval containing left end
  Interval right() const;     ///< returns interval containing right end

  template <typename T_Scalar>
  bool contains( const T_Scalar & A_X ) const;     ///< checks if interval contains given point X
  bool contains( const Interval & A_iv ) const;  ///< checks if interval contains given interval iv

  template <typename T_Scalar>
  bool containsInInterior( const T_Scalar & A_X ) const;    ///< checks if interval contains in interior given point X
  bool containsInInterior( const Interval & A_iv ) const; ///< checks if interval contains in interior given interval iv

  bool subset( const Interval & A_iv ) const;          ///< checks if interval is subset of iv
  bool subsetInterior( const Interval & A_iv ) const;  ///< checks if interval is subset of interior of iv
  friend bool subset(const Interval & A_iv1, const Interval & A_iv2)
  { return A_iv1.subset(A_iv2); }
  friend bool subsetInterior(const Interval & A_iv1, const Interval & A_iv2)
  { return A_iv1.subsetInterior(A_iv2); }

  Interval mid() const;           ///< returns middle point of interval
  /// Splits interval into the form  mid + remainder, where mid - is middle point
  void split( Interval & A_rMid, Interval & A_rRemainder ) const;
  void split( BoundType & A_rMid, Interval & A_rRemainder ) const;
  void split(Interval &r) { split(*this, r); }

  // "Constants" (but they depend on the bound type and the precision)
  static Interval pi();     ///< returns pi constant
  static Interval euler();  ///< returns euler constant

  //================ definitions in intervalOp.hpp ============================

  Interval & operator = ( const Interval & A_iv );
  Interval & operator = ( const BoundType & A_x);
  Interval & operator += ( const Interval & A_iv );
  Interval & operator -= ( const Interval & A_iv );
  Interval & operator *= ( const Interval & A_iv );
  Interval & operator /= ( const Interval & A_iv );

  //================ definitions in intervalFriend.h ============================
  /* // DOES NOT WORK in GCC because left, right, etc are also member functions ????
    //    The way to avoid this is to give names capd::intervals::left
    //    but it generates warning in Intel compiler.
  /// returns interval containing left end
  friend Interval left <>( const Interval & A_iv );
  /// returns interval containing right end
  friend Interval right <>( const Interval & A_iv );
  /// returns left end
  friend BoundType leftBound <>( const Interval & A_iv );
  /// returns right end
  friend BoundType rightBound <>( const Interval & A_iv );
   */

  friend bool operator == <> ( const Interval & A_iv1, const Interval & A_iv2 );
  friend bool operator <= <> ( const Interval & A_iv1, const Interval & A_iv2 );
  friend bool operator >= <> ( const Interval & A_iv1, const Interval & A_iv2 );
  friend bool operator <  <> ( const Interval & A_iv1, const Interval & A_iv2 );
  friend bool operator >  <> ( const Interval & A_iv1, const Interval & A_iv2 );
  friend bool operator != <> ( const Interval & A_iv1, const Interval & A_iv2 );


  //==== declarations in intervalFriend.h  definitions in intervalOp.hpp ==================

  friend Interval operator - <>(const Interval& A_iv);

  friend Interval operator + <>(const Interval& A_iv1, const Interval& A_iv2);
  friend Interval operator - <>(const Interval& A_iv1, const Interval& A_iv2);
  friend Interval operator * <>(const Interval& A_iv1, const Interval& A_iv2);
  friend Interval operator / <>(const Interval& A_iv1, const Interval& A_iv2);
  friend Interval operator ^ <>(const Interval& A_iv1, int i);

  friend std::ostream & operator << <>(std::ostream& s, const Interval & A_iv);
  friend std::istream & operator >> <>(std::istream& s, Interval & A_iv);

  //================ definitions in intervalFun.hpp ============================
  static T_Bound computeExpError();
  static T_Bound computeSinError();
  static T_Bound computeAtanError();

  /// Taylor series length used in the EXP function
  static const int S_nExpTaylorOrder = 20;

  /// Taylor series length used in the LOG function, it MUST be an EVEN value
  static const int S_nLogTaylorOrder = 40;

  /// Taylor series length used in the SIN function, it MUST be an ODD value
  static const int S_nSinTaylorOrder = 11;

  /// Taylor series length used in the ATAN function, it MUST be an ODD value
  static const int S_nAtanTaylorOrder = 21 ;

  // Definitions of friend functions: relations and arithmetic operators
  //  between interval and BoundType
  // To provide implicite conversions they cannot be defined outside the class
  // and here only declared
#include "capd/intervals/Interval_FriendInternal.h"

#ifdef __INTERVAL_DEPRECATED__
  const T_Bound & left_b(void) const { return leftBound(); }
  const T_Bound & right_b(void) const { return rightBound(); }
#endif // __INTERVAL_DEPRECATED__

protected:
  BoundContainer   m_left,    ///< left end of an interval
                   m_right;   ///< right end of an interval
};



//================ definitions in intervalFun.hpp ============================

template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> diam(const Interval< T_Bound, T_Rnd>& );

template < typename T_Bound, typename T_Rnd>
inline Interval< T_Bound, T_Rnd> mid(const Interval< T_Bound, T_Rnd>& A_iv)
{
  return  A_iv.mid();
}

//  Intersection of two intervals
template < typename T_Bound, typename T_Rnd>
bool  intersection( Interval< T_Bound, T_Rnd> A_iv1,
    Interval< T_Bound, T_Rnd> A_iv2,
    Interval< T_Bound, T_Rnd> &A_rIntersection);

// returns an interval containing iv1 and iv2
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> intervalHull(const Interval< T_Bound, T_Rnd> & A_iv1,
    const Interval< T_Bound, T_Rnd> & A_iv2);

//  On output:  iv \subset Mid + [-diam , diam]
template < typename T_Bound, typename T_Rnd>
void split( Interval< T_Bound, T_Rnd> & A_iv,
    Interval< T_Bound, T_Rnd> & A_rMid,
    T_Bound & A_diam);

template < typename T_Bound, typename T_Rnd>
inline void split(Interval< T_Bound, T_Rnd>& A_rIv, T_Bound & A_diam)
{
  split(A_rIv, A_rIv, A_diam);
}

template < typename T_Bound, typename T_Rnd>
inline bool isSingular(const Interval< T_Bound, T_Rnd>& A_x)
{
  return ((A_x.leftBound()<=0) && (A_x.rightBound()>=0));
}


// returns x^n
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> power (const Interval< T_Bound, T_Rnd> & x, int n);

// returns a^b
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> power (const Interval< T_Bound, T_Rnd> & a,
    const Interval< T_Bound, T_Rnd> & b);

// square root of x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> sqrt (const Interval< T_Bound, T_Rnd> &x);

// sin x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd>  sin (const Interval< T_Bound, T_Rnd>& x);

// cos x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> cos (const Interval< T_Bound, T_Rnd>& x);

// tan x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> tan (const Interval< T_Bound, T_Rnd>& x);

// cot x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> cot (const Interval< T_Bound, T_Rnd>& x);

// atan x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> atan (const Interval< T_Bound, T_Rnd>& x);

// asin x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> asin (const Interval< T_Bound, T_Rnd>& x);

// acos x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> acos (const Interval< T_Bound, T_Rnd>& x);

// sinh x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> sinh (const Interval< T_Bound, T_Rnd>& x);

// cosh x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> cosh (const Interval< T_Bound, T_Rnd>& x);

// tanh x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> tanh (const Interval< T_Bound, T_Rnd>& x);

// coth x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> coth (const Interval< T_Bound, T_Rnd>& x);

// exp x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> exp (const Interval< T_Bound, T_Rnd> & x);

// natural logarithm of x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> log (const Interval< T_Bound, T_Rnd>& x);

// solves inclusion a+[0,t]*p\subset c for t
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> solveAffineInclusion(const Interval< T_Bound, T_Rnd> & a,
    const Interval< T_Bound, T_Rnd> & p,
    const Interval< T_Bound, T_Rnd> & c);
// solves inclusion a+[0,t]*p\subset c for t
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> solveAffineInclusion(const Interval< T_Bound, T_Rnd> & a,
    const Interval< T_Bound, T_Rnd> & p,
    const Interval< T_Bound, T_Rnd> & c,
    int & dir);

// square of x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> sqr (const Interval< T_Bound, T_Rnd> &x){
  return power(x,2);
}

/// returns nonnegative part of interval
/// @remark if nonnegative part is empty throws exception
template < typename T_Bound, typename T_Rnd>
inline Interval< T_Bound, T_Rnd > nonnegativePart(const Interval< T_Bound, T_Rnd > &iv)
{
  if(iv.rightBound() < 0.0)
    throw IntervalError<T_Bound>(" Nonnegative part is empty! ", iv.leftBound(), iv.rightBound());
  return Interval< T_Bound, T_Rnd >(capd::max(iv.leftBound(), T_Bound(0.0)), iv.rightBound());
}

/// Ball with center iv and radius r
template < typename T_Bound, typename T_Rnd>
inline Interval< T_Bound, T_Rnd > ball(const Interval< T_Bound, T_Rnd > &iv,
    const Interval< T_Bound, T_Rnd > &r)
    {
  return Interval< T_Bound, T_Rnd >(iv.leftBound() - r.rightBound(),
      iv.rightBound() + r.rightBound());
    }

/// Ball with center iv and radius r
template < typename T_Bound, typename T_Rnd>
inline Interval< T_Bound, T_Rnd > ball(const Interval< T_Bound, T_Rnd > &iv,
    const T_Bound &r)
    {
  return Interval< T_Bound, T_Rnd >(iv.leftBound() - r, iv.rightBound() + r);
    }


/// an absolute value
template < typename T_Bound, typename T_Rnd>
inline intervals::Interval< T_Bound, T_Rnd> iabs (const intervals::Interval< T_Bound, T_Rnd>& A_inter)
{
  T_Bound left = capd::abs(A_inter.leftBound());
  T_Bound right = capd::abs(A_inter.rightBound());

  if(left > right)
  {
    T_Bound temp = left;   left = right;   right = temp;
  }

  if(A_inter.contains(0.0))
    left= 0.0;

  return intervals::Interval< T_Bound, T_Rnd>(left,right);

} // abs


///maximum
template < typename T_Bound, typename T_Rnd>
inline intervals::Interval< T_Bound, T_Rnd> imax (
    const intervals::Interval< T_Bound, T_Rnd>& A_iv1,
    const intervals::Interval< T_Bound, T_Rnd>& A_iv2
){
  return intervals::Interval< T_Bound, T_Rnd>(
      (A_iv1.leftBound()>A_iv2.leftBound() ? A_iv1.leftBound() : A_iv2.leftBound()),
      (A_iv1.rightBound()>A_iv2.rightBound() ? A_iv1.rightBound() : A_iv2.rightBound())
  );
}

///minimum
template < typename T_Bound, typename T_Rnd>
inline intervals::Interval< T_Bound, T_Rnd> imin (
    const intervals::Interval< T_Bound, T_Rnd>& A_iv1,
    const intervals::Interval< T_Bound, T_Rnd>& A_iv2
){
  return intervals::Interval< T_Bound, T_Rnd>(
      (A_iv1.leftBound()<A_iv2.leftBound() ? A_iv1.leftBound() : A_iv2.leftBound()),
      (A_iv1.rightBound()<A_iv2.rightBound() ? A_iv1.rightBound() : A_iv2.rightBound())
  );
}

/// @}

}} // namespace capd::intervals

namespace capd{
/**
 * Specialization of TypeTraits for intervals
 */
template <typename T, typename R>
class TypeTraits < ::capd::intervals::Interval<T,R> > {
public:
  typedef T Real;

  static inline const ::capd::intervals::Interval<T,R> & zero(){
    return S_zero;
  }
  static inline const ::capd::intervals::Interval<T,R> & one(){
    return S_one;
  }
  static inline int numberOfDigits(){
    return TypeTraits<T>::numberOfDigits();
  }
  /// Machine epsilon (the difference between 1 and the least value greater than 1 that is representable).
  static inline T epsilon() throw(){
    return TypeTraits<T>::epsilon();
  }
  /// this flag is true for all interval types
  static const bool isInterval = true;

private:
  static const  ::capd::intervals::Interval<T,R> S_zero ;// = capd::intervals::Interval<T,R>(T(0.0));
  static const  ::capd::intervals::Interval<T,R> S_one ;
};

template <typename T, typename R>
const ::capd::intervals::Interval<T,R> TypeTraits< ::capd::intervals::Interval<T,R> >::S_zero = ::capd::intervals::Interval<T,R>(
    TypeTraits<T>::zero()
);

template <typename T, typename R>
const ::capd::intervals::Interval<T,R> TypeTraits< ::capd::intervals::Interval<T,R> >::S_one = ::capd::intervals::Interval<T,R>(
    TypeTraits<T>::one()
);

/// an absolute value
template < typename T_Bound, typename T_Rnd>
inline intervals::Interval< T_Bound, T_Rnd> abs (const intervals::Interval< T_Bound, T_Rnd>& A_inter) {
  return ::capd::intervals::iabs(A_inter);
} // abs


///maximum
template < typename T_Bound, typename T_Rnd>
inline intervals::Interval< T_Bound, T_Rnd> max (
    const intervals::Interval< T_Bound, T_Rnd>& A_iv1,
    const intervals::Interval< T_Bound, T_Rnd>& A_iv2
) {
  return ::capd::intervals::imax(A_iv1, A_iv2);
}

///minimum
template < typename T_Bound, typename T_Rnd>
inline intervals::Interval< T_Bound, T_Rnd> min (
    const intervals::Interval< T_Bound, T_Rnd>& A_iv1,
    const intervals::Interval< T_Bound, T_Rnd>& A_iv2
){
  return ::capd::intervals::imin(A_iv1, A_iv2);
}



} // namespace capd

/////////////////////////////////////////////////////////////////////
//    inline functions
/////////////////////////////////////////////////////////////////////

// base functions - constructors, converters,...
#include "capd/intervals/Interval_Base.h"

// deprecated functions
#include "capd/intervals/Interval_Deprecated.h"

// operators
#ifdef __INTERVAL_SPEED_OPTIMIZED__
#include "capd/intervals/Interval_Op.hpp"
#endif

template < typename T_Bound, typename T_Rnd>
inline bool isInf(const capd::intervals::Interval< T_Bound, T_Rnd >& r) {
  return (isInf(r.leftBound()) || isInf(r.rightBound()));
}


#endif // _CAPD_INTERVAL_INTERVALINTF_H_
