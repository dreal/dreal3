/////////////////////////////////////////////////////////////////////////////
/// @file Interval_Fun.hpp
///
/// Interval Arithmetics - elementary functions
///  such as: sin, cos, tan, exp, log, power,...
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_INTERVAL_INTERVALFUN_HPP_
#define _CAPD_INTERVAL_INTERVALFUN_HPP_

#include <iostream>
#include <cmath>
#include <limits>

using std::sqrt;
using std::log;

namespace capd{
namespace intervals{

  
///////////////////////////////////////////////////////////////////////////////
// positivePower
///
/// a computation of value^{exponent} with current rounding settings
///  (exponent has to be positive)
///
///////////////////////////////////////////////////////////////////////////////
template <typename T_Bound>
T_Bound positivePower (T_Bound value, unsigned exponent)
{
  T_Bound result = 1;

  while (exponent)
  {
    while (!(exponent & 1))
    {
      exponent >>= 1;
      value *= value;
    }
    exponent--;
    result *= value;
  }

  return result;
}

///////////////////////////////////////////////////////////////////////////////
//  computeExpError
///
/// an estimation for the remainder term during computation of "exp"
///////////////////////////////////////////////////////////////////////////////

template < typename T_Bound, typename T_Rnd>
T_Bound Interval< T_Bound, T_Rnd>::computeExpError()
{
  // we start with a computation of the factorial, with rounding down because we divide by it later
  T_Rnd::roundDown();
  T_Bound factorial = 1;
  for (int i = 2; i <= S_nExpTaylorOrder + 1; ++i)
  {
    factorial *= (T_Bound) i;
  }

  // now we divide with up rounding
  T_Rnd::roundUp ();

  return euler().rightBound() / factorial;
} // Interval::computeExpError

///////////////////////////////////////////////////////////////////////////////
//  ComputeSinError
///
///  An estimation of the remainder term for  "sin"
///
// remark It should be possible to use here the same approach as for the 'log'
// function, because we have here a series with alternating signs, and the
// absolute value of each term decreases to 0. Maybe we should do it this way
// in the future. - P. Pilarczyk
///////////////////////////////////////////////////////////////////////////////

template < typename T_Bound, typename T_Rnd>
T_Bound Interval< T_Bound, T_Rnd>::computeSinError()
{
  // we start with a computation of the factorial, with rounding down because
  // we divide by it later

  T_Rnd::roundDown ();
  T_Bound factorial = 1;
  for (int i = 2; i <= 2 * S_nSinTaylorOrder + 2; ++i)
  {
    factorial *= (T_Bound) i;
  }

  // now we compute powers and quotient with rounding up
  T_Rnd::roundUp ();
  // the number 1.5708 > pi/2 - this overestimates a little the remainder
  return positivePower( T_Bound(1.5708), 2 * S_nSinTaylorOrder + 2) / factorial;

} // Interval::computeSinError

///////////////////////////////////////////////////////////////////////////////
//  ComputeAtanError
///
///  An estimation of the remainder term for  "atan" for |x|<(sqrt(2)-1)
// (Added by Hiroyuki Inou in October 2007)
///////////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
T_Bound Interval< T_Bound, T_Rnd>::computeAtanError()
{
  // now we compute powers and quotient with rounding up
  T_Rnd::roundUp ();
  // the number 0.41422 > sqrt(2)-1 - this overestimates a little the remainder
  return positivePower( T_Bound(0.41422), 2 * S_nAtanTaylorOrder + 3) / (2 * S_nAtanTaylorOrder + 3);

} // Interval::computeAtanError

///////////////////////////////////////////////////////////////////////////////
//  diam
///
/// diameter of an interval
///////////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> diam(const Interval< T_Bound, T_Rnd>& A_iVal)
{
  return Interval< T_Bound, T_Rnd>(A_iVal.rightBound()-A_iVal.leftBound());
}

///////////////////////////////////////////////////////////////////////////////
// intersection
///
/// Intersection of two intervals
///
/// @param[in] A_iv1, A_iv2 two intervals
/// @param[out] A_rInter intersection of A_iv1 and A_iv2 (if non empty)
///
/// @returns  if common part of iv1 and iv2 is nonempty then
///              inter =intersection of iv1 and iv2 and true is returned
///              otherwise false is returned and inter is untouched
///////////////////////////////////////////////////////////////////////////////

template < typename T_Bound, typename T_Rnd>
bool  intersection( Interval< T_Bound, T_Rnd> A_iv1,
                    Interval< T_Bound, T_Rnd> A_iv2,
                    Interval< T_Bound, T_Rnd> &A_rInter)
{
  T_Bound left = (A_iv1.leftBound() > A_iv2.leftBound())? A_iv1.leftBound() : A_iv2.leftBound();
  T_Bound right = (A_iv1.rightBound() < A_iv2.rightBound())? A_iv1.rightBound(): A_iv2.rightBound();

  if(left <= right) // is intersection nonempty ?
  {
  A_rInter = Interval< T_Bound, T_Rnd>(left, right);
  return true;
  }
  else
    return false;
} // intersection

/// returns an interval containing A_iv1 and A_iv2
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> intervalHull( const Interval< T_Bound, T_Rnd> & A_iv1,
                      const Interval< T_Bound, T_Rnd> & A_iv2)
{
  T_Bound left = (A_iv1.leftBound() < A_iv2.leftBound())? A_iv1.leftBound() : A_iv2.leftBound(),
          right = (A_iv1.rightBound() >A_iv2.rightBound())? A_iv1.rightBound() : A_iv2.rightBound();
  return Interval< T_Bound, T_Rnd>(left, right);

}

///  On output:  \f$ iv \subset Mid + [-diam , diam] \f$
template < typename T_Bound, typename T_Rnd>
void split( Interval< T_Bound, T_Rnd> & A_iv,
            Interval< T_Bound, T_Rnd> & A_rMid,
            T_Bound & A_diam)
{
  T_Rnd::roundUp();
  T_Bound m = (A_iv.rightBound() + A_iv.leftBound()) /2,
          l = m - A_iv.leftBound(),
          r = A_iv.rightBound() - m;
  A_rMid = Interval<T_Bound, T_Rnd>(m);
  A_diam = ( l > r) ? l : r;
} // split


///////////////////////////////////////////////////////////////////////////////
//   power(Interval, int)
///
///  a computation of base^{exponent}
///
///////////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> power(const Interval< T_Bound, T_Rnd> & base, int exponent)
{
  T_Bound left,
          right;
  int sign=1;
  if(exponent < 0 )
  {
    sign=0;
    exponent = -exponent;
  }

  /* if 'exponent' is even, then we need to correct the ends of Interval -
     only absolute values matter*/
  Interval<T_Bound, T_Rnd> value = (exponent % 2 == 0)? capd::abs(base) : base;

  if(value.rightBound() > 0)
  {
    T_Rnd::roundUp();
    right = positivePower (value.rightBound(), exponent);
  }
  else if(value.rightBound() < 0)
  {
    T_Rnd::roundDown();
    right = -positivePower(-value.rightBound(), exponent);
  }
  else
    right = T_Bound(0.0);  // we do not check here if exponent == 0 it will be checked when computing left end.

  if(value.leftBound() > 0)
  {
    T_Rnd::roundDown();
    left = positivePower (value.leftBound(), exponent);
  }
  else if(value.leftBound() < 0)
  {
    T_Rnd::roundUp();
    left = -positivePower (-value.leftBound(), exponent);
  }
  else if(exponent != 0)
    left = T_Bound(0.0);
  else
      throw IntervalError<T_Bound>(" power(x, n): n == 0  and x contains 0. \n", base.leftBound(), base.rightBound());

  Interval< T_Bound, T_Rnd> out(left, right);

  if(sign==0)  // when an exponent is negative
  {
    out = Interval< T_Bound, T_Rnd>(1.0)/out;
  }

   return out;

} // power(Interval, int)

///////////////////////////////////////////////////////////////////////////////
//   power(Interval, Interval)
///
///  a computation of a^b
///
///////////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> power(const Interval< T_Bound, T_Rnd> &a, const Interval< T_Bound, T_Rnd> &b)
{
  if( a.leftBound() < 0 )
    throw IntervalError<T_Bound>(" power(A, B): Interval A must be nonnegative. \n", a.leftBound(), a.rightBound());

  return exp(b * log(a));
} // power(Interval, Interval)


//using std::sqrt;
///////////////////////////////////////////////////////////////////////////////
//   sqrt
///
/// square root of x
///////////////////////////////////////////////////////////////////////////////

template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> sqrt(const Interval< T_Bound, T_Rnd> &x)
{
  if( x.leftBound() < 0 )
    throw IntervalError<T_Bound>(" sqrt(x): Interval x must be nonnegative. \n", x.leftBound(), x.leftBound());

// Strange: needed for T_Bound=double, declaration outside the function causes errors in gcc 4.2.1
using std::sqrt;

  T_Rnd::roundDown();
  T_Bound l = sqrt(x.leftBound());

  T_Rnd::roundUp();
  T_Bound r = sqrt(x.rightBound());

  return Interval< T_Bound, T_Rnd> (l, r);
} // sqrt



//////////////////////////////////////////////////////////////////////////
//    Trigonometric functions for interval arguments
//////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////
//   scaledSin2
///
/// a rigorous computation of sin(x) for  0 <= x <= pi
///
/// @remark  if x<0 , then we compute sin(x=0)
/// @remark  we expect x to be a point interval
//////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> scaledSin2 (const Interval< T_Bound, T_Rnd> & x)
{
  static T_Bound S_SinError = Interval< T_Bound, T_Rnd>::computeSinError();

  if (x <= 0)
    return Interval< T_Bound, T_Rnd> (0);

  Interval< T_Bound, T_Rnd> h = power( x - (Interval< T_Bound, T_Rnd>::pi()/T_Bound(2.0)), 2);
  Interval< T_Bound, T_Rnd> res (1.0);

  for(int i = Interval< T_Bound, T_Rnd>::S_nSinTaylorOrder; i>0; --i)
    res = 1 - ( h/(2*i * (2*i-1)) ) * res;

  intersection( Interval< T_Bound, T_Rnd>(-1, 1),
                res + Interval< T_Bound, T_Rnd>(T_Bound(0.0), S_SinError),
                res);
  return (res);

} // scaledSin2

//////////////////////////////////////////////////////////////////////////
//   scaledSin1
///
/// the function computes sin(x) for \f$ x \subset [0,\infty] \f$
///
//////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> scaledSin1 (const Interval< T_Bound, T_Rnd> &x)
{
  Interval< T_Bound, T_Rnd> pi = Interval< T_Bound, T_Rnd>::pi(),
                            piby2 = pi / Interval< T_Bound, T_Rnd>(2),
                            pi3by2 = pi * Interval< T_Bound, T_Rnd>(1.5);

  if (x.leftBound() <= piby2.rightBound())  // left end is to the left of pi/2
  {
    if (x.rightBound() >= pi3by2.leftBound())
      return Interval< T_Bound, T_Rnd> (-1, 1); // because [Pi/2 , 3Pi/2] \subset x

    if (x.rightBound() >= pi.leftBound()) //  [pi/2,Pi] \subset x, but x < 3*pi/2
      return Interval< T_Bound, T_Rnd>(
               -(scaledSin2 ((x.rightBound() - pi).right()).rightBound()),
               T_Bound(1.0)
      );

    if (x.rightBound() >= piby2.leftBound()) // x \subset [0, pi) and  pi/2 \in x
      return Interval< T_Bound, T_Rnd>(
          scaledSin2( Interval< T_Bound, T_Rnd>(::capd::min(x.leftBound(),  (pi-x.rightBound()).leftBound()))).leftBound(),
               T_Bound(1.0)
      );

    // sin is an increasing function on x \subset [0, pi/2]
    return Interval< T_Bound, T_Rnd> (
         scaledSin2(x.left()).leftBound(),
         scaledSin2(x.right()).rightBound()
    );
  }

  //  we know that x > pi/2
  if (x.leftBound() <= pi.rightBound()) // Left(x) < pi
  {
    if (x.rightBound() >= (2.5*pi).leftBound())
      return Interval< T_Bound, T_Rnd> (-1, 1); // because [pi,5*pi/2] \subset x

    if (x.rightBound() >= (pi*2).leftBound()) //   [pi,2*pi] \subset x
      return Interval< T_Bound, T_Rnd> (
        T_Bound(-1.0),
        ::capd::max( scaledSin2(x.left()).rightBound(),
                     scaledSin2((x-(pi*2)).right()).rightBound())
      );

    // now we know that  x < 2*pi and  pi/2 < Left(x) < pi
    // hence  sinus achieves maximum on Left(x)
    T_Bound rsin = ::capd::max (scaledSin2 (x.left()).rightBound(), T_Bound(0.0));
    // ?? Why max is needed

    // if 3*pi/2 \n x then minumum of sin(x)=-1
    if (x.rightBound() >= pi3by2.leftBound())
      return Interval< T_Bound, T_Rnd> (T_Bound(-1.0), rsin);

    // otherwise minimum is achieved at right(x)
    if (x.rightBound() >= pi.leftBound())
    {
      // we have to shift  an argument to use scaledSin2
      return Interval< T_Bound, T_Rnd> (
                      -(scaledSin2((x.right() - pi).right()).rightBound()),
                      rsin
      );
    }
    else
      return Interval< T_Bound, T_Rnd> (
               ::capd::max(scaledSin2(x.right()).leftBound(), T_Bound(0.0)),
               rsin
      );
  }
  // we know that \pi < x
  return - scaledSin1 (x - pi);

} // scaledSin1

/// sinus of x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> sin (const Interval< T_Bound, T_Rnd> &x)
{

  Interval< T_Bound, T_Rnd> pi2 = Interval< T_Bound, T_Rnd>::pi() * Interval< T_Bound, T_Rnd>(2.0);

  if (diam(x).rightBound() >= pi2.leftBound())
    return Interval< T_Bound, T_Rnd> (-1, 1);

  // we shift x by 2*pi*k as close to zero as possible, we want x to be positive
  // after this shift
  long k;

  T_Rnd::roundUp();
  if (x.leftBound() > 0)
  {
    T_Bound temp = x.leftBound() / pi2.rightBound();
    if(temp > std::numeric_limits<long>::max())
      return Interval< T_Bound, T_Rnd> (-1, 1);
    k = toLongInt(temp);
  }
  else
  {
    T_Bound temp = (-x.leftBound()) / pi2.rightBound() + 1;
    if(temp < std::numeric_limits<long>::min())
      return Interval< T_Bound, T_Rnd> (-1, 1);
    k = - toLongInt(temp);
  }
  Interval< T_Bound, T_Rnd> y = x - Interval< T_Bound, T_Rnd>(k) * pi2;

  if (y.leftBound() < 0.)
    while (y.leftBound() < 0.)
      y += pi2;
  else
    while (y.leftBound() >= pi2.rightBound())
      y -= pi2;

  if (diam(y).rightBound() >= pi2.leftBound())
    return Interval< T_Bound, T_Rnd> (-1., 1.);

  return scaledSin1 (y);
} // sin

/// cosinus of x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> cos(const Interval< T_Bound, T_Rnd> &x)
{
  return sin((Interval< T_Bound, T_Rnd>::pi()*Interval< T_Bound, T_Rnd>(0.5))-x);
}

/// tangens of x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> tan(const Interval< T_Bound, T_Rnd> &x)
{
  return sin(x)/sin((Interval< T_Bound, T_Rnd>::pi()*Interval< T_Bound, T_Rnd>(0.5))-x);
}

/// cotangens of x
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> cot(const Interval< T_Bound, T_Rnd>& x)
{
  return sin(Interval< T_Bound, T_Rnd>::pi()*Interval< T_Bound, T_Rnd>(0.5)-x)/sin(x);
}

//////////////////////////////////////////////////////////////////////////
//   scaledAtan2
///
/// a rigorous computation of atan(x) for  0 <= x <= sqrt(2)-1
///
/// @remark  if x<0 , then we compute sin(x=0)
/// @remark  we expect x to be a point interval
// (Added by Hiroyuki Inou in October 2007)
//////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> scaledAtan2 (const Interval< T_Bound, T_Rnd> & x)
{
  static T_Bound S_AtanError = Interval< T_Bound, T_Rnd>::computeAtanError();

  if (x <= 0)
    return Interval< T_Bound, T_Rnd> (0);

  Interval< T_Bound, T_Rnd> h = power(x,2);
  Interval< T_Bound, T_Rnd> res (1.0);
  res = res/(2*Interval< T_Bound, T_Rnd>::S_nAtanTaylorOrder+1);

  for(int i = Interval< T_Bound, T_Rnd>::S_nAtanTaylorOrder; i>0; --i)
    res = Interval< T_Bound, T_Rnd>(1.0)/(2*i-1) - res * h;

  res = res*x;

  return (res + Interval< T_Bound, T_Rnd>(T_Bound(0.0), S_AtanError));

} // scaledAtan2

//////////////////////////////////////////////////////////////////////////
//   scaledAtan1
///
/// a rigorous computation of atan(x) for  0 <= x
///
/// @remark  if x<0 , then we compute sin(x=0)
/// @remark  we expect x to be a point interval
// (Added by Hiroyuki Inou in October 2007)
//////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> scaledAtan1 (const Interval< T_Bound, T_Rnd> & x)
{
    int n=0;
    Interval< T_Bound, T_Rnd> y(x);
    // if x > sqrt(2)-1, then use atan(x)=2*atan((sqrt(1+x^2)-1)/x)
    const T_Bound s2_1 = (sqrt (Interval< T_Bound, T_Rnd> (2.0, 2.0)) - 1.0).rightBound();
    while ( y >= s2_1 ) {
  y = (sqrt(1+power(y,2))-1)/y;
  n++;
    }
    return (power(Interval< T_Bound, T_Rnd>(2.0),n)*
      Interval< T_Bound, T_Rnd>(
    scaledAtan2(Interval< T_Bound, T_Rnd>(y.leftBound())).leftBound(),
    scaledAtan2(Interval< T_Bound, T_Rnd>(y.rightBound())).rightBound()));

} // scaledAtan1

/// arctangens of x
// (Added by Hiroyuki Inou in October 2007)
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> atan (const Interval< T_Bound, T_Rnd> &x)
{
  int sign=1;
  Interval< T_Bound, T_Rnd> y(x);

  // if x is negative, then compute -atan(-x)
  if (x.rightBound() < 0)
  {
      sign=0;
      y = -x;
  } else
  // if x contains 0, then compute the bounds separately
  if (x.leftBound() < 0)
  {
      return Interval< T_Bound, T_Rnd>(
    -scaledAtan1(Interval< T_Bound, T_Rnd>(-x.leftBound())).rightBound(),
    scaledAtan1(Interval< T_Bound, T_Rnd>(x.rightBound())).rightBound() );
  }

  Interval< T_Bound, T_Rnd> res(
      scaledAtan1(Interval< T_Bound, T_Rnd>(y.leftBound())).leftBound(),
      scaledAtan1(Interval< T_Bound, T_Rnd>(y.rightBound())).rightBound());
  if (sign == 0) // when x is negative
  {
      res = -res;
  }

  return (res);

} // atan

//////////////////////////////////////////////////////////////////////////
//   scaledAsin1
///
/// A rigorous computation of asin(x) far from -1 and 1
///  i.e. for -0.7 <= x <=  0.7
///
/// @remark  we expect x to be a point interval
//////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
inline Interval< T_Bound, T_Rnd> scaledAsin1 (const Interval< T_Bound, T_Rnd> &x){
  return (atan(x/sqrt(1-power(x,2))));
}

//////////////////////////////////////////////////////////////////////////
//   scaledAsin2
///
/// A rigorous computation of asin(x) for   0.7 < x <=1
///
/// we use: asin(x) = pi/2 - atan(sqrt(1-x^2) / x)
/// @remark  we expect x to be a point interval
//////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
inline Interval< T_Bound, T_Rnd> scaledAsin2 (const Interval< T_Bound, T_Rnd> &x){
  return (Interval< T_Bound, T_Rnd>::pi()/2-atan(sqrt(nonnegativePart(1-power(x,2)))/x));
}

template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> pointAsin (const Interval< T_Bound, T_Rnd> &x){
  const T_Bound border = 0.8;
  if (x < -border)
    return -scaledAsin2<T_Bound, T_Rnd>(-x);
  else if (x.leftBound()>border)
    return scaledAsin2<T_Bound, T_Rnd>(x);
  else
    return scaledAsin1<T_Bound, T_Rnd>(x);
}

// asin
// (Added by Hiroyuki Inou in October 2007)
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> asin (const Interval< T_Bound, T_Rnd> &x)
{
  // x must satisfy -1 <= x <= 1
  if ( ( x.leftBound() < -1 ) || ( x.rightBound() > 1) )
    throw IntervalError<T_Bound>(" asin(A): Interval A must satisfy -1 <= A <= 1. \n", x.leftBound(), x.rightBound());

  // we use monotonicity of asin and compute value on the interval ends.
  Interval< T_Bound, T_Rnd> l = pointAsin(x.left()),
                            r = pointAsin(x.right());

  return Interval< T_Bound, T_Rnd>(l.leftBound(), r.rightBound());
}

//////////////////////////////////////////////////////////////////////////
//   scaledAcos
///
/// A rigorous computation of acos(x) for point intervals
///
/// @remark  we expect x to be a point interval
//////////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> scaledAcos(const Interval< T_Bound, T_Rnd> &x){

  const T_Bound border = 1./8.;

  if (x.rightBound() < 0) {
    return Interval< T_Bound, T_Rnd>::pi() - scaledAcos(-x);
  } else if(x.leftBound()< border) {
    return (Interval< T_Bound, T_Rnd>::pi()/2-atan(x/sqrt(1-power(x,2))));
  } else {
    return (atan(sqrt(1-power(x,2))/x));
  }
}

// acos
// (Added by Hiroyuki Inou in October 2007)
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> acos (const Interval< T_Bound, T_Rnd> &x)
{
  // x must satisfy -1 <= x <= 1
  if ( ( x.leftBound() < -1 ) || ( x.rightBound() > 1) )
    throw IntervalError<T_Bound>(" acos(A): Interval A must satisfy -1 <= A <= 1. \n", x.leftBound(), x.rightBound());
   return Interval< T_Bound, T_Rnd>(
       scaledAcos(x.right()).leftBound(),
       scaledAcos(x.left()).rightBound());
}

//////////////////////////////////////////////////////////////////////////
//      Interval hyperbolic functions
//////////////////////////////////////////////////////////////////////////

/// sinh
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> sinh(const Interval< T_Bound, T_Rnd> &x)
{
  return ( (exp(x)-exp(-x))/Interval< T_Bound, T_Rnd>(2) );
}

/// cosh
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> cosh(const Interval< T_Bound, T_Rnd> &x)
{
  return ( (exp(x)+exp(-x))/Interval< T_Bound, T_Rnd>(2) );
}

/// tanh
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> tanh(const Interval< T_Bound, T_Rnd> &x)
{
  return ( (exp(x)-exp(-x))/(exp(x)+exp(-x)) );
}

/// coth
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> coth(const Interval< T_Bound, T_Rnd> &x)
{
  return ( (exp(x)+exp(-x))/(exp(x)-exp(-x)) );
}


//////////////////////////////////////////////////////////////////////
//     an exponent function
//////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
//   scaledExp
///
/// returns exp(x) for x in [0,1] with actual rounding
///
/// @remark do not add taylor expansion errors to upper  bounds.
//////////////////////////////////////////////////////////////////////
template <typename T_Bound>
T_Bound scaledExp (T_Bound x, int expTaylorOrder)
{
  T_Bound res = 0;
  for (int i = expTaylorOrder; i > 0; --i )
    res = (res + 1.0) * (x / i);
  return res + 1;
} // scaledExp


//////////////////////////////////////////////////////////////////////
//   exp
///
/// returns exp(x)
///
/// @remark do not add taylor expansion errors to upper  bounds.
//////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> exp (const Interval< T_Bound, T_Rnd> &x)
{
  static T_Bound S_ExpError = Interval< T_Bound, T_Rnd>::computeExpError();
  Interval< T_Bound, T_Rnd> e = Interval< T_Bound, T_Rnd>::euler();

  T_Bound left_res, right_res;
  if(x.rightBound()>100000.) // exp(100000) > max long double number
    right_res = std::numeric_limits<T_Bound>::infinity();
  else
  {
    // we compute first upper bound - this depends on right(x)

    // we decompose right(x)= right_int + right_diff
    //   where right_int is an integer
    //         right_diff - a fractional part - in [0,1]
    T_Bound right_x = x.rightBound();
    int right_int = toInt(right_x);
    while (right_int > right_x)
    {
      right_int --;
    }
    // a fractional part of right(x)

    T_Rnd::roundUp();
    T_Bound right_diff = right_x - right_int;
    T_Bound base;
    if (right_int >= 0)
      base = e.rightBound();
    else
    {
      base = 1.0 / e.leftBound();
      right_int = -right_int;
    }

    T_Rnd::roundUp();
    right_res = positivePower(base, right_int) *
      (scaledExp(right_diff, Interval< T_Bound, T_Rnd>::S_nExpTaylorOrder)+ S_ExpError);
  }

  // now we compute lower bound - this depends on Left(x)

  T_Bound left_x = x.leftBound();
  if(left_x < -100000.)
    left_res = 0.;
  else
  {
    int left_int = toInt(left_x);
    while (left_int > left_x)
    {
      left_int --;
    }
    T_Rnd::roundDown();
    T_Bound left_diff = left_x - left_int;
    T_Bound base;
    if (left_int >= 0)
      base = e.leftBound();
    else
    {
      base = 1.0 / e.rightBound();
      left_int = -left_int;
    }

    T_Rnd::roundDown();
    left_res = positivePower(base, left_int) * scaledExp(left_diff, Interval< T_Bound, T_Rnd>::S_nExpTaylorOrder);
  }
  return Interval< T_Bound, T_Rnd> (left_res, right_res);
} // exp


//////////////////////////////////////////////////////////////////////
//      the natural logarithm function
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//   scaledLogUp
///
/// computes upper bound for log(1+x) for \f$ x \in [0,1/2] \f$
/// @remark the constant S_LogTaylorOrder must be even
///         round UP mode needs to be set
//////////////////////////////////////////////////////////////////////
template <typename T_Bound>
T_Bound scaledLogUp (const T_Bound & x, int logTaylorOrder)
{
  T_Bound result = 1.0;
  result /= (logTaylorOrder + 1);
  for (int i = logTaylorOrder; i > 0; i -= 2)
    result = (result * x + (-1.0) / i) * x + 1.0 / (i - 1);
  return result * x;
} // scaledLogUp

// needed for Interval<double>
// using ::std::log;

//////////////////////////////////////////////////////////////////////
//   scaledLogDown
///
/// computes lower bound for log(1+x) for \f$ x \in [0,1/2] \f$
/// @remark the constant S_LogTaylorOrder must be even
///         round down mode needs to be set
//////////////////////////////////////////////////////////////////////
template <typename T_Bound>
T_Bound scaledLogDown (const T_Bound &x, int logTaylorOrder)
{
  T_Bound result = 0.0;
  for (int i = logTaylorOrder; i > 0; i -= 2)
    result = result * x * x + 1.0 / (i - 1) + (-x) / i;
  return result * x;
} //scaledLogDown

//////////////////////////////////////////////////////////////////////
//   log
///
/// computes natural logarithm of x,  x>0
///
//////////////////////////////////////////////////////////////////////
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> log (const Interval< T_Bound, T_Rnd> &x)
{
  if( x.leftBound()<=0.0 )
  {
   throw std::range_error("log(): domain error.\n");
  }
  static const Interval< T_Bound, T_Rnd> one_and_a_half (3.0 / 2, 3.0 / 2);
  static const Interval< T_Bound, T_Rnd> log_one_and_a_half( 0.4054651081081643,
                                                             0.4054651081081645);
  using std::log;
  T_Bound right_result, y, y_prim, d;
  int k;
  
  if(isInf(x.rightBound()))
    right_result = x.rightBound();
  else
  {
    // we take an advantage of monotonicty

    // an upper estimate -
    // we find an integer 'k' such that right(x)=(1.5)^k*d , where d is in [1,1.5]
    T_Rnd::roundNearest();
    k = toInt( floor (log (x.rightBound()) / log (1.5)));

    // we find a lower bound for  (1.5)^k
    if (k >= 0)
    {
      T_Rnd::roundDown();
      y = positivePower (3.0 / 2, k);
    }
    else
    {
      T_Rnd::roundUp();
      y = positivePower (3.0 / 2, -k);
      T_Rnd::roundDown ();
      y = 1.0 / y;
    }

    // try to increase k if possible
    T_Rnd::roundDown ();
    y_prim = y * (3.0 / 2);
    while (y_prim < x.rightBound())
    {
      k++;
      y = y_prim;
      y_prim = y * (3.0 / 2);
    }

    // decrease k if too big
    while (y > x.rightBound())
    { 
      k --;
      y /= (3.0 / 2);
    }

    // computes upper bound for d
    T_Rnd::roundUp ();
    d = x.rightBound() / y;

    // computation of an upper bound for k*log(1.5) + log(d)
    T_Rnd::roundUp ();
    right_result = scaledLogUp(d - 1, Interval< T_Bound, T_Rnd>::S_nLogTaylorOrder );

    T_Rnd::roundUp ();
    right_result += ((k > 0) ? log_one_and_a_half.rightBound() :
      log_one_and_a_half.leftBound()) * k;
  } // end rightBound(x)!=infinity

  // now we proceed analogously with the left end
  k = toInt(floor((log (x.leftBound()) / log (1.5))));

  // upper bound for (1.5)^k
  if (k >= 0)
  {
    T_Rnd::roundUp();
    y = positivePower (3.0 / 2, k);
  }
  else
  {
    T_Rnd::roundDown();
    y = positivePower (3.0 / 2, -k);
    T_Rnd::roundUp ();
    y = 1.0 / y;
  }

  // increase k if possiblle
  T_Rnd::roundUp ();
  y_prim = y * (3.0 / 2);
  while (y_prim < x.leftBound())
  {
    k ++;
    y = y_prim;
    y_prim = y * (3.0 / 2);
  }

  // decrease k if too large
  while (y > x.leftBound())
  {
    k --;
    y /= (3.0 / 2);
  }

  // computation of lower bound for d
  T_Rnd::roundDown ();
  d = x.leftBound() / y;

  // computation of lower bound for   log (1.5) * k + log d
  T_Rnd::roundDown ();
  T_Bound left_result = scaledLogDown (d-1, Interval< T_Bound, T_Rnd>::S_nLogTaylorOrder);

  T_Rnd::roundDown ();
  left_result +=((k > 0) ? log_one_and_a_half.leftBound() :
    log_one_and_a_half.rightBound()) * k;

  return Interval< T_Bound, T_Rnd> (left_result, right_result);
} // log



/// solves inclusion  \f$ a+[0,t]*p\subset c for t \f$
template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> solveAffineInclusion(const Interval< T_Bound, T_Rnd> & a,
                                               const Interval< T_Bound, T_Rnd> & p,
                                               const Interval< T_Bound, T_Rnd> & c)
{
  typedef Interval< T_Bound, T_Rnd> Interval;
  Interval t;
  if ( !(a.subset(c)) )
  {
 #ifdef DEBUGGING
    throw IntervalError<T_Bound>("Cannot solve affine inclusion", a.leftBound(), a.rightBound());
 #endif

  }
  else
  {
    if(p>=0)
      t = ((c.right() - a.right()) / p.right()).left();
    else if(p<=0)
      t =((c.left() - a.left()) / p.left()).left();
    else{
      T_Bound t1 = ((c.right() - a.right()) / p.right()).leftBound();
      T_Bound t2 = ((c.left() - a.left()) / p.left()).leftBound();
      t = Interval( ( t1<t2 ? t1 : t2 ) );
    }
 }
 return(t);
} // solveAffineInclusion(Interval&, Interval&, Interval&)

template < typename T_Bound, typename T_Rnd>
Interval< T_Bound, T_Rnd> solveAffineInclusion(const Interval< T_Bound, T_Rnd> & a,
                                               const Interval< T_Bound, T_Rnd> & p,
                                               const Interval< T_Bound, T_Rnd> & c,
                                               int & dir)
{
  typedef Interval< T_Bound, T_Rnd> Interval;
   Interval t;
   if ( !(a.subset(c)) ){
 #ifdef DEBUGGING
     throw IntervalError<T_Bound>("Cannot solve affine inclusion", a.leftBound(), a.rightBound());
 #endif
  }
  else
  {
    if(p>=0)
    {
      dir=1;
      t = ((c.right() - a.right()) / p.right()).left();
    }
    else if(p<=0)
    {
      dir=-1;
      t =((c.left() - a.left()) / p.left()).left();
    }
    else{
      T_Bound t1 = ((c.right() - a.right()) / p.right()).leftBound();
      T_Bound t2 = ((c.left() - a.left()) / p.left()).leftBound();
      if( t1 < t2 )
      {
        dir=1;
        t=Interval(t1);
      }else{
        dir=-1;
        t=Interval(t2);
      }
    }
  }
  return(t);
} // solveAffineInclusion(Interval&, Interval&, Interval&, int&)

}} // namespace capd::intervals

#endif // _CAPD_INTERVAL_INTERVALFUN_HPP_
