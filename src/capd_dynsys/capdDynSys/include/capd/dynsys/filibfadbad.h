//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file filibfadbad.h
///
/// @author Tomasz Kapela   @date 2010-10-11
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_DYNSYS_FILIBFADBAD_H_
#define _CAPD_DYNSYS_FILIBFADBAD_H_
#include "capd/filib/Interval.h"
#include "capd/fadbad/fadbad.h"

namespace fadbad{

  template <typename BoundType, capd::filib::RoundingStrategy R, capd::filib::IntervalMode M>
  struct Op < capd::filib::Interval<BoundType, R, M > >
  {
    typedef capd::filib::Interval<BoundType, R, M > Base;
    typedef capd::filib::Interval<BoundType, R, M > T;

    static Base myInteger(const int i) { return Base(BoundType(i)); }
    static Base myZero() { return capd::TypeTraits<Base>::zero(); }
    static Base myOne() { return capd::TypeTraits<Base>::one();}
    static Base myTwo() { return myInteger(2); }
    static Base myPI() { return Base::pi(); }
    static T myPos(const T& x) { return +x; }
    static T myNeg(const T& x) { return -x; }
    template <typename U> static T& myCadd(T& x, const U& y) { return x+=y; }
    template <typename U> static T& myCsub(T& x, const U& y) { return x-=y; }
    template <typename U> static T& myCmul(T& x, const U& y) { return x*=y; }
    template <typename U> static T& myCdiv(T& x, const U& y) { return x/=y; }
    static T myInv(const T& x) { return myOne()/x; }
    static T mySqr(const T& x) { return sqr(x); }
    template <typename X, typename Y>
    static T myPow(const X& x, const Y& y) { return power(x,y); }
    static T mySqrt(const T& x) { return sqrt(x); }
    static T myLog(const T& x) { return log(x); }
    static T myExp(const T& x) { return exp(x); }
    static T mySin(const T& x) { return sin(x); }
    static T myCos(const T& x) { return cos(x); }
    static T myTan(const T& x) { return tan(x); }
    static T myAsin(const T& x) { return asin(x); }
    static T myAcos(const T& x) { return acos(x); }
    static T myAtan(const T& x) { return atan(x); }
    static bool myEq(const T& x, const T& y) { return x==y; }
    static bool myNe(const T& x, const T& y) { return x!=y; }
    static bool myLt(const T& x, const T& y) { return x<y; }
    static bool myLe(const T& x, const T& y) { return x<=y; }
    static bool myGt(const T& x, const T& y) { return x>y; }
    static bool myGe(const T& x, const T& y) { return x>=y; }
  };
} // end of namespace fadbad

#endif // _CAPD_FILIB_FILIBFADBAD_H_
