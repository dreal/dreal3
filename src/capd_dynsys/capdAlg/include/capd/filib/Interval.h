/////////////////////////////////////////////////////////////////////////////
//
/// @file filib/Interval.h
///
/// @author Tomasz Kapela   @date 2010-06-08
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_FILIB_INTERVAL_H_
#define _CAPD_FILIB_INTERVAL_H_
#include <interval/interval.hpp>
#include "capd/intervals/IntervalError.h"
#include "capd/auxil/minmax.h"
#include "capd/basicalg/TypeTraits.h"

// #define __FILIB_DEPRECATED__

namespace capd{
namespace filib{

/**
   Supported rounding strategies:

   - ::filib::native_switched:   do switching as called from interval and reset afterwards
   - ::filib::native_directed:   native_switched without reset
   - ::filib::multiplicative:    multiplicate with pred/succ of 0/1
   - ::filib::no_rounding:       don't set rounding at all
   - ::filib::pred_succ_rounding:          use pred and succ
*/
typedef ::filib::rounding_strategy RoundingStrategy;

/**
 * interval computation mode
 *
 * Possible values:
 * -  ::filib::i_mode_normal
 * -  ::filib::i_mode_extended
 * -  ::filib::i_mode_extended_flag
 *
 **/
typedef ::filib::interval_mode IntervalMode;

template <typename T, RoundingStrategy R, IntervalMode M>
class Interval;

template <typename T, RoundingStrategy R, IntervalMode M>
inline Interval<T, R, M> diam(const Interval<T, R, M> & ix);

}

/// absolute values of all elements of a given interval
template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
filib::Interval<T, R, M> abs (const filib::Interval<T, R, M> & A_inter);

/// maximum
template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
inline filib::Interval<T, R, M> max(const filib::Interval<T, R, M>& A_iv1, const filib::Interval<T, R, M>& A_iv2);

///minimum
template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
inline filib::Interval<T, R, M> min (const filib::Interval<T, R, M>& A_iv1, const filib::Interval<T, R, M>& A_iv2);

/// fast interval library
namespace filib{

//typedef ::filib::interval<double, ::filib::native_directed > T;
// typedef filib::interval<double> T;

////////////////////////////////////////////////////////////////////////////////////////
//  capd::filib::Interval
///
///
/// CAPD interface for fast interval library filib
///
/// This template class has three parameters
/// - T - type of endpoints,
/// - R - rounding policy (\see RoundingStrategy for possible values),
/// - M - interval mode  (\see IntervalMode for possible values).
/// It works as an adapter for the other CAPD routines.
/// It has exactly the same interface as native CAPD interval
/// and it just calls the corresponding functions from the filib.
///
///  Most common used intervals (they can be used as T parameter of a Interval template)
///  -  Interval<double, ::filib::native_directed >  - intervals with double endpoints that switch rounding and do not restore rounding after each operation,
///  -  Interval<double, ::filib::native_switched >  - intervals with double endpoints that switch rounding and restore rounding 'to nearest' after each operation,
///  -  Interval<double, ::filib::native_switched, filib::i_mode_extended >  - extended. exception free intervals with double endpoints that can handle empty intervals, unbounded intervals.
///
/// To prevent misusing and enable easy interchange of a different interval implementation
/// the filib interval T is not a base class of the Interval class
/// and can be accesed only by getBaseInterval() method.
///
//////////////////////////////////////////////////////////////////////////////////////////

template <typename T, RoundingStrategy R = ::filib::native_directed, IntervalMode M = ::filib::i_mode_normal>
class Interval{
public:
  typedef ::filib::interval<T, R, M > BaseInterval;
  typedef typename BaseInterval::value_type BoundType;
  typedef ::filib::fp_traits<T, R> RoundingPolicy;
  typedef capd::intervals::IntervalError<BoundType> IntervalError;
  static const IntervalMode mode = M;

protected:
  BaseInterval m_interval;
public:

  inline Interval(){}

  /// copying constructor
  inline Interval( const Interval & A_iv ) : m_interval(A_iv.m_interval){
  }

  /// constructor from any class that can be coverted to BoundType
  // template < typename T_Scalar >
  // Interval( const T_Scalar & A_scalar );
  Interval(const BoundType & A_scalar) : m_interval(A_scalar){
  }

  /// constructor from any class that can be coverted to BoundType
  //template < typename T_Scalar1, typename T_Scalar2 >
  //Interval( const T_Scalar1 & A_left, const T_Scalar2 & A_right );
  Interval( const BoundType & A_left, const BoundType & A_right ) : m_interval(A_left, A_right){
  }

  Interval( const BaseInterval & interval) : m_interval(interval){
  }

  Interval(const char left[], const char right[]) : m_interval(std::string(left), std::string(right)){
  }

  Interval(const std::string & left, const std::string & right) : m_interval(left, right){
  }

  /**
   *  returns reference to base (filib) interval
   */
  BaseInterval & getBaseInterval(){
    return m_interval;
  }

  /**
   *  returns const reference to base (filib) interval
   */
  const BaseInterval & getBaseInterval() const {
    return m_interval;
  }
  /**
   *  sets up floting point unit.
   *  It has to be called before first use of intervals
   */
  static void setup(){
    BaseInterval::traits_type::setup();
  }
  /**
   *  resets default rounding mode (to the nearest)
   */
  static void reset(){
    BaseInterval::traits_type::reset();
  }

#ifdef __FILIB_DEPRECATED__
  /**
   get current output precision
   */
  static int const & precision(){
    return BaseInterval::precision();
  }
  /**
   set output precision and return old precision
   */
  static int precision (int const & newprec){
    return BaseInterval::precision( newprec);
  }
#endif


  const BoundType & leftBound() const  ///<  returns the left end of the interval
      {  return m_interval.inf(); }
  const BoundType & rightBound() const ///<  returns the right end of the interval
      { return m_interval.sup(); }

  friend inline const BoundType & leftBound(const Interval & x)  ///<  returns the left end of the interval
      {  return x.m_interval.inf(); }
  friend inline const BoundType & rightBound(const Interval & x)  ///<  returns the right end of the interval
      { return x.m_interval.sup(); }

  const BoundType & inf() const  ///<  returns the left end of the interval
      {  return m_interval.inf(); }
  const BoundType & sup() const ///<  returns the right end of the interval
      { return m_interval.sup(); }

  friend inline const BoundType & inf(const Interval & x)  ///<  returns the left end of the interval
      {  return x.m_interval.inf(); }
  friend inline const BoundType & sup(const Interval & x)  ///<  returns the right end of the interval
      { return x.m_interval.sup(); }

  /// @deprecated
  void setLeftBound(const BoundType & A_left)
      { m_interval = BaseInterval(A_left, m_interval.sup());}
  /// @deprecated
  void setRightBound(const BoundType & A_right)
      { m_interval = BaseInterval( m_interval.inf(), A_right);}

  Interval left() const      ///< returns interval containing left end
      { return Interval(m_interval.inf()); }
  Interval right() const     ///< returns interval containing right end
      { return Interval(m_interval.sup()); }

  friend inline Interval left(const Interval & x)      ///< returns interval containing left end
      { return Interval(x.m_interval.inf()); }
  friend inline Interval right(const Interval & x)     ///< returns interval containing right end
      { return Interval(x.m_interval.sup()); }

  template <typename T_Scalar>
  bool contains( const T_Scalar & A_X ) const     ///< checks if interval contains given point X
      { return m_interval.contains(A_X); }
  bool contains( const Interval & A_iv ) const  ///< checks if interval contains given interval iv
      { return A_iv.m_interval.subset(m_interval); }
  template <typename T_Scalar>
  bool containsInInterior( const T_Scalar & A_X ) const     ///< checks if interval contains in interior given point X
      { return (leftBound() < (BoundType)A_X) && ((BoundType)A_X < rightBound()); }

  bool containsInInterior( const Interval & A_iv ) const    ///< checks if interval contains in interior given interval iv
      { return ((leftBound() < A_iv.leftBound()) && (A_iv.rightBound() < rightBound())); }

  bool subset( const Interval & A_iv ) const          ///< checks if interval is subset of iv
      { return m_interval.subset(A_iv.m_interval); }
  bool subsetInterior( const Interval & A_iv ) const  ///< checks if interval is subset of interior of iv
      { return m_interval.interior(A_iv.m_interval); }
  friend bool subset(const Interval & A_iv1, const Interval & A_iv2)
      { return A_iv1.subset(A_iv2); }
  friend bool subsetInterior(const Interval & A_iv1, const Interval & A_iv2)
      { return A_iv1.subsetInterior(A_iv2); }

  Interval mid() const           ///< returns middle point of interval
      { return Interval(m_interval.mid()); }
  Interval abs() const           ///<Returns the interval of absolute values of this interval, i.e.
      { return Interval(m_interval.abs()); }
  /// Splits interval into the form  mid + remainder, where mid - is middle point
  void split( Interval & A_rMid, Interval & A_rRemainder ) const {
    BoundType m = m_interval.mid();
    A_rRemainder.m_interval = m_interval - m;
    A_rMid.m_interval = m;
  }
  void split( BoundType & A_rMid, Interval & A_rRemainder ) const {
    A_rMid = m_interval.mid();
    A_rRemainder.m_interval = m_interval - A_rMid;
  }
  void split(Interval &r)
      { split(*this, r); }

  // "Constants" (but they depend on the bound type and the precision)
  static Interval pi();     ///< returns pi constant
  static Interval euler();  ///< returns euler constant

  Interval & operator = ( const Interval & A_iv ){
    m_interval = A_iv.m_interval;
    return *this;
  }
  Interval & operator = ( const BoundType & A_x){
    m_interval = A_x;
    return *this;
  }
  Interval & operator += ( const Interval & A_iv ){
    m_interval += A_iv.m_interval;
    return *this;
  }
  Interval & operator -= ( const Interval & A_iv ){
    m_interval -= A_iv.m_interval;
    return *this;
  }
  Interval & operator *= ( const Interval & A_iv ){
    m_interval *= A_iv.m_interval;
    return *this;
  }
  Interval & operator /= ( const Interval & A_iv ){
    m_interval /= A_iv.m_interval;
    return *this;
  }

  friend bool operator ==  ( const Interval & A_iv1, const Interval & A_iv2 ) {
    return ((A_iv1.leftBound()==A_iv2.leftBound()) && (A_iv1.rightBound()==A_iv2.rightBound()));
  }
  friend bool operator <=  ( const Interval & A_iv1, const Interval & A_iv2 ) {
    return (A_iv1.rightBound() <= A_iv2.leftBound());
  }
  friend bool operator >=  ( const Interval & A_iv1, const Interval & A_iv2 ) {
    return (A_iv1.leftBound()>= A_iv2.rightBound() );
  }
  friend bool operator <   ( const Interval & A_iv1, const Interval & A_iv2 ) {
    return (A_iv1.rightBound() < A_iv2.leftBound());
  }
  friend bool operator >   ( const Interval & A_iv1, const Interval & A_iv2 ) {
    return (A_iv1.leftBound()> A_iv2.rightBound());
  }
  friend bool operator !=  ( const Interval & A_iv1, const Interval & A_iv2 ) {
    return ((A_iv1.leftBound()!= A_iv2.leftBound()) || (A_iv1.rightBound() != A_iv2.rightBound()));
  }


  ///  operator == (interval, scalar)
  friend inline bool operator == (const Interval & A_iVal1, const BoundType & A_Val2) {
    return ((A_iVal1.leftBound() == (A_Val2)) && (A_iVal1.rightBound() == (A_Val2)));
  }

  ///  operator == (scalar, interval)
  friend inline bool operator == (const BoundType & A_Val1, const Interval & A_iVal2) {
     return ((A_Val1 == A_iVal2.leftBound()) && (A_Val1 == A_iVal2.rightBound()));
  }

  ///  operator !=  (interval, scalar)
  friend inline bool operator != (const Interval & A_iVal1, const BoundType & A_Val2) {
    return ((A_iVal1.leftBound() != A_Val2) || (A_iVal1.rightBound() != A_Val2));
  }

  ///  operator !=   (scalar, interval)
  friend inline bool operator != (const BoundType & A_Val1, const Interval & A_iVal2) {
     return ((A_Val1 != A_iVal2.leftBound()) || (A_Val1 != A_iVal2.rightBound()));
  }

  ///  operator >  (interval, scalar)
  friend inline bool operator > (const Interval & A_iVal1,  const BoundType & A_Val2) {
     return (A_iVal1.leftBound() > A_Val2);
  }

  ///  operator >   (scalar, interval)
  friend inline bool operator > (const BoundType & A_Val1, const Interval & A_iVal2) {
     return (A_Val1 > A_iVal2.rightBound());
  }

  ///  operator >= (interval, scalar)
  friend inline bool operator >= (const Interval & A_iVal1, const BoundType & A_Val2) {
     return (A_iVal1.leftBound() >= A_Val2);
  }

  ///  operator >=  (scalar, interval)
  friend inline bool operator >= (const BoundType & A_Val1, const Interval & A_iVal2) {
     return (A_Val1 >= A_iVal2.rightBound());
  }

  ///  operator  < (interval, scalar)
  friend inline bool operator < (const Interval & A_iVal1, const BoundType & A_Val2) {
     return (A_iVal1.rightBound() < A_Val2);
  }

  ///  operator  <  (scalar, interval)
  friend inline bool operator < (const BoundType & A_Val1, const Interval & A_iVal2) {
     return (A_Val1 < A_iVal2.leftBound());
  }

  /// operator <=  (interval, scalar)
  friend inline bool operator <= (const Interval & A_iVal1, const BoundType & A_Val2) {
     return (A_iVal1.rightBound() <= A_Val2);
  }

  /// operator <=  (scalar, interval)
  friend inline bool operator <= (const BoundType & A_Val1, const Interval & A_iVal2) {
     return (A_Val1 <= A_iVal2.leftBound());
  }

//==== declarations in intervalFriend.h  definitions in intervalOp.hpp ==================

  friend Interval operator - (const Interval& A_iv){
    return Interval(-A_iv.m_interval);
  }
  friend Interval operator + (const Interval& A_iv1, const Interval& A_iv2) {
    return Interval(A_iv1.m_interval + A_iv2.m_interval);
  }
  friend Interval operator - (const Interval& A_iv1, const Interval& A_iv2) {
    return Interval(A_iv1.m_interval - A_iv2.m_interval);
  }
  friend Interval operator * (const Interval& A_iv1, const Interval& A_iv2) {
    return Interval(A_iv1.m_interval * A_iv2.m_interval);
  }
  friend Interval operator / (const Interval& A_iv1, const Interval& A_iv2) {
    if(! A_iv2.contains(capd::TypeTraits<BoundType>::zero())){
      return Interval(A_iv1.m_interval / A_iv2.m_interval);
    } else {
      throw typename Interval::IntervalError("Division by 0 in operator/(Interval, Interval)", A_iv2.inf(),  A_iv2.sup());
    }

  }
  friend Interval operator ^ (const Interval& A_iv1, int i) {
    return Interval(power(A_iv1.m_interval, i));
  }


  //////////////////////////////////////////////////////////////////////////
  //  ARITHMETIC OPERATORS between interval and BoundType
  //////////////////////////////////////////////////////////////////////////


  /// operator +  (interval, scalar)
  friend inline Interval operator+ (const Interval & A_iVal, const BoundType &A_x) {
    return Interval(A_iVal.m_interval + A_x);
  }

  /// operator + (scalar, interval)
  friend inline Interval operator+ (const BoundType & A_x, const Interval & A_iVal) {
    return Interval(A_x + A_iVal.m_interval);
  }

  /// operator -  (interval, scalar)
  friend inline Interval operator- (const Interval & A_iVal, const BoundType &A_x) {
    return Interval(A_iVal.m_interval - A_x);
  }

  /// operator - (scalar, interval)
  friend inline Interval operator- (const BoundType & A_x, const Interval & A_iVal) {
    return Interval(A_x - A_iVal.m_interval);
  }

  /// operator * (interval, scalar)
  friend inline Interval operator* (const Interval & A_iVal, const BoundType &A_x) {
    return Interval(A_iVal.m_interval * A_x);
  }

  /// operator * (scalar, interval)
  friend inline Interval operator* (const BoundType & A_x, const Interval & A_iVal) {
    return Interval(A_x * A_iVal.m_interval);
  }

  /// operator / (scalar, interval)
  friend inline Interval operator/ (const Interval & A_iVal, const BoundType &A_x) {
    if(A_x != capd::TypeTraits<BoundType>::zero()){
      return Interval(A_iVal.m_interval / A_x);
    } else {
      throw typename Interval::IntervalError("Division by 0 in operator/(Interval, BoundType)", A_x, A_x);
    }
  }

  /// operator / (interval, scalar)
  friend inline Interval operator/ (const BoundType & A_x, const Interval & A_iVal) {
    if(! A_iVal.contains(capd::TypeTraits<BoundType>::zero())){
      return Interval(A_x / A_iVal.m_interval);
    } else {
      throw typename Interval::IntervalError("Division by 0 in operator/(BoundType, Interval)", A_iVal.inf(),  A_iVal.sup());
    }
  }

  friend std::ostream & operator << (std::ostream& s, const Interval & A_iv){
	//Interval::precision(s.precision());
    s << "[" << A_iv.m_interval.inf() << ", " << A_iv.m_interval.sup() <<"]";
    return s;
  }

  friend std::istream & operator >> (std::istream& s, Interval & A_iv){
    s >> A_iv.m_interval;
    return s;
  }

#ifdef __INTERVAL_DEPRECATED__
  const BoundType & left_b(void) const { return leftBound(); }
  const BoundType & right_b(void) const { return rightBound(); }
#endif // __INTERVAL_DEPRECATED__





//================ definitions in intervalFun.hpp ============================


  friend Interval diam<>(const Interval & ix);
// {
//    return ix.m_interval.diam();
//  }

  friend inline Interval mid(const Interval& A_iv){
  return  A_iv.mid();
}

  ///  Intersection of two intervals
  friend bool  intersection( const Interval & A_iv1,
                             const Interval & A_iv2,
                             Interval & A_rIntersection){
     BoundType left = (A_iv1.leftBound() > A_iv2.leftBound())? A_iv1.leftBound() : A_iv2.leftBound();
     BoundType right = (A_iv1.rightBound() < A_iv2.rightBound())? A_iv1.rightBound(): A_iv2.rightBound();

     if(left <= right) // is intersection nonempty ?
     {
     A_rIntersection = Interval(left, right);
     return true;
     }
     else
       return false;
   } // intersection

  /// returns an interval containing ix and iy
  friend Interval intervalHull(const Interval & ix,
                                       const Interval & iy){
    BoundType left = (ix.leftBound() < iy.leftBound())? ix.leftBound() : iy.leftBound(),
             right = (ix.rightBound() >iy.rightBound())? ix.rightBound() : iy.rightBound();
     return Interval(left, right);
  }

//  On output:  iv \subset Mid + [-diam , diam]

  friend inline void split( Interval & A_iv,
            Interval & A_rMid,
            BoundType & A_diam) {
    /// TODO : correct to not switch rounding
//     T_Rnd::roundUp();
//     T_Bound m = (A_iv.rightBound() + A_iv.leftBound()) /2,
//             l = m - A_iv.leftBound(),
//             r = A_iv.rightBound() - m;
//     A_rMid = Interval<T_Bound, T_Rnd>(m);
//     A_diam = ( l > r) ? l : r;

     BoundType m = A_iv.m_interval.mid();
     Interval t = A_iv - m;
     A_rMid = Interval(m);
     A_diam = ( t.leftBound() > t.rightBound()) ? t.leftBound() : t.rightBound();
  }


  friend inline void split(Interval& A_rIv, BoundType & A_diam) {
    //split(A_rIv, A_rIv, A_diam);
    BoundType m = A_rIv.m_interval.mid();
        Interval t = A_rIv - m;
        A_rIv = Interval(m);
        A_diam = ( t.leftBound() > t.rightBound()) ? t.leftBound() : t.rightBound();
  }


  friend inline bool isSingular(const Interval& A_x) {
    return ((A_x.leftBound()<=0) && (A_x.rightBound()>=0));
  }


// returns x^n

  friend inline Interval power (const Interval & x, int n){
     return Interval(power(x.m_interval, n));

  }

// returns a^b

  friend inline Interval power (const Interval & a,
                         const Interval & b){
    if( a.leftBound() >= 0 ){
       return Interval(pow(a.m_interval, b.m_interval));
    } else
          throw typename Interval::IntervalError(" power(A, B): Interval A must be nonnegative. \n", a.leftBound(), a.rightBound());

  }


// square root of x

  friend inline Interval sqrt (const Interval &x){

    if( x.leftBound() < 0 )
      throw typename Interval::IntervalError(" sqrt(x): Interval x must be nonnegative. \n", x.leftBound(), x.leftBound());

    return Interval(sqrt(x.m_interval));
  }


// sin x

  friend inline Interval  sin (const Interval& x){
    return Interval(sin(x.m_interval));
  }

// cos x

  friend inline Interval cos (const Interval& x){
    return Interval(cos(x.m_interval));
  }

// tan x

friend inline Interval tan (const Interval& x){
  return Interval(tan(x.m_interval));
}

// cot x

friend inline Interval cot (const Interval& x){
  return Interval(cot(x.m_interval));
}

// atan x

friend inline Interval atan (const Interval& x){
  return Interval(atan(x.m_interval));
}

// asin x

friend inline Interval asin (const Interval& x){
  // x must satisfy -1 <= x <= 1
  if ( ( x.leftBound() < -1 ) || ( x.rightBound() > 1) )
    throw typename Interval::IntervalError(" asin(A): Interval A must satisfy -1 <= A <= 1. \n", x.leftBound(), x.rightBound());

  return Interval(asin(x.m_interval));
}

// acos x

friend inline Interval acos (const Interval& x){
  // x must satisfy -1 <= x <= 1
  if ( ( x.leftBound() < -1 ) || ( x.rightBound() > 1) )
    throw typename Interval::IntervalError(" acos(A): Interval A must satisfy -1 <= A <= 1. \n", x.leftBound(), x.rightBound());

  return Interval(acos(x.m_interval));
}

// sinh x

friend inline Interval sinh (const Interval& x){
  return Interval(sinh(x.m_interval));
}

// cosh x

friend inline Interval cosh (const Interval& x){
  return Interval(cosh(x.m_interval));
}

// tanh x

friend inline Interval tanh (const Interval& x){
  return Interval(tanh(x.m_interval));
}

// coth x

friend inline Interval coth (const Interval& x){
  return Interval(coth(x.m_interval));
}

// exp x

friend inline Interval exp (const Interval & x){
  return Interval(exp(x.m_interval));
}

// natural logarithm of x

friend inline Interval log (const Interval& x){
  if( x.leftBound()<=0.0 )
    throw typename Interval::IntervalError(" log(A): Interval A must satisfy 0 < A. \n", x.leftBound(), x.rightBound());

  return Interval(log(x.m_interval));
}


// square of x

friend inline Interval sqr (const Interval &x){
  return Interval(sqr(x.m_interval));
}


/// returns nonnegative part of interval
/// @remark if nonnegative part is empty throws exception

friend inline Interval nonnegativePart(const Interval &iv){
  if(iv.rightBound() < 0.0)
    throw typename Interval::IntervalError(" Nonnegative part is empty! ", iv.leftBound(), iv.rightBound());
  return Interval(capd::max(iv.leftBound(), BoundType(0.0)), iv.rightBound());
}

/// Ball with center iv and radius r

friend inline Interval ball(const Interval &iv,
                            const Interval & r)
{
    return Interval(iv.leftBound() - r.rightBound(),
                    iv.rightBound() + r.rightBound());
}

/// Ball with center iv and radius r

friend inline Interval ball(const Interval &iv,
                            const BoundType &r)
{
    return Interval(iv.leftBound() - r, iv.rightBound() + r);
}


/// solves inclusion a+[0,t]*p\subset c for t
friend Interval solveAffineInclusion(const Interval & a,
                              const Interval & p,
                              const Interval & c){
  Interval t;
  if ( !(a.subset(c)) ) {

    throw typename Interval::IntervalError("Cannot solve affine inclusion", a.leftBound(), a.rightBound());

  } else if(p >= 0) {
      t = ((c.right() - a.right()) / p.right()).left();
  } else if(p<=0) {
      t = ((c.left() - a.left()) / p.left()).left();
  } else {
      typename Interval::BoundType t1 = ((c.right() - a.right()) / p.right()).leftBound();
      typename Interval::BoundType t2 = ((c.left() - a.left()) / p.left()).leftBound();
      t = Interval( ( t1<t2 ? t1 : t2 ) );
  }
  return t;
} // solveAffineInclusion(Interval&, Interval&, Interval&)

/// solves inclusion a+[0,t]*p\subset c for t
friend Interval solveAffineInclusion(const Interval & a,
                              const Interval & p,
                              const Interval & c,
                              int & dir) {
  Interval t;
  if ( !(a.subset(c)) ) {
    throw typename Interval::IntervalError("Cannot solve affine inclusion", leftBound(a), rightBound(a));

  } else if(p >= 0) {

    t = ((c.right() - a.right()) / p.right()).left();
    dir = 1;

  } else if(p<=0) {

    t = ((c.left() - a.left()) / p.left()).left();
    dir = -1;

  } else {

    typename Interval::BoundType t1 = ((c.right() - a.right()) / p.right()).left();
    typename Interval::BoundType t2 = ((c.left() - a.left()) / p.left()).left();
    if( t1 < t2 ){
      dir=1;
      t=Interval(t1);
    } else {
      dir=-1;
      t=Interval(t2);
    }
  }
  return t;
}



};  // end of class Interval

template <typename T, RoundingStrategy R, IntervalMode M>
Interval<T, R, M> diam(const Interval<T, R, M> & ix){
    return ix.m_interval.diam();
}


}} // namespace capd::intervals

namespace capd{

/**
 * Specialization for intervals
 */
template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
class TypeTraits < capd::filib::Interval<T, R, M> > {
public:
  typedef  T Real;

  static inline const ::capd::filib::Interval<T, R, M> & zero(){
    return S_zero;
  }
  static inline const ::capd::filib::Interval<T, R, M> & one(){
    return S_one;
  }
  static inline int numberOfDigits(){
    return TypeTraits<T>::numberOfDigits();
  }
  /// Machine epsilon (the difference between 1 and the least value greater than 1 that is representable).
  static inline T epsilon() throw(){
    return TypeTraits<T>::epsilon();
  }

  static const bool isInterval = true;

private:
  static const  ::capd::filib::Interval<T, R, M> S_zero ;// = ::capd::filib::Interval<T,R>(T(0.0));
  static const  ::capd::filib::Interval<T, R, M> S_one ;
};

template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
const ::capd::filib::Interval<T, R, M> TypeTraits< ::capd::filib::Interval<T, R, M> >::S_zero = ::capd::filib::Interval<T, R, M>(
    TypeTraits<T>::zero()
);

template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
const ::capd::filib::Interval<T, R, M> TypeTraits< ::capd::filib::Interval<T, R, M> >::S_one = ::capd::filib::Interval<T, R, M>(
    TypeTraits<T>::one()
);


/// an absolute value

template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
inline filib::Interval<T, R, M> abs (const filib::Interval<T, R, M> & A_inter)
{
   return filib::Interval<T, R, M>(A_inter.abs());

} // abs


///maximum
template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
inline filib::Interval<T, R, M> max (
                                     const filib::Interval<T, R, M> & A_iv1,
                                     const filib::Interval<T, R, M> & A_iv2)
{
   return filib::Interval<T, R, M>(
                  (A_iv1.leftBound()>A_iv2.leftBound() ? A_iv1.leftBound() : A_iv2.leftBound()),
                  (A_iv1.rightBound()>A_iv2.rightBound() ? A_iv1.rightBound() : A_iv2.rightBound())
          );
}

///minimum
template <typename T, filib::RoundingStrategy R, filib::IntervalMode M>
inline filib::Interval<T, R, M> min (const filib::Interval<T, R, M>& A_iv1,
                                                 const filib::Interval<T, R, M>& A_iv2)
{
   return filib::Interval<T, R, M>(
                  (A_iv1.leftBound()<A_iv2.leftBound() ? A_iv1.leftBound() : A_iv2.leftBound()),
                  (A_iv1.rightBound()<A_iv2.rightBound() ? A_iv1.rightBound() : A_iv2.rightBound())
          );
}






//////////////////////////////////////////////////////////////////////////
//        CONSTANTS
//////////////////////////////////////////////////////////////////////////
namespace filib{


template <typename T, RoundingStrategy R, IntervalMode M>
inline Interval<T, R, M> Interval<T, R, M>::pi() {
  return Interval<T, R, M>( 3.1415926535897932, 3.1415926535897934 );
}

template <typename T, RoundingStrategy R, IntervalMode M>
inline Interval<T, R, M> Interval<T, R, M>::euler() {
   return Interval<T, R, M>( 2.7182818284590452, 2.7182818284590454 );
}



}} // end of namespace capd::filib

#endif // _CAPD_FILIB_INTERVAL_H_
