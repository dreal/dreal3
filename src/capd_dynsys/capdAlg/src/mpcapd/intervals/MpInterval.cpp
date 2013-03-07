/////////////////////////////////////////////////////////////////////////////
/// @file MpInterval.cpp
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _MP_INTERVAL_CPP_
#define _MP_INTERVAL_CPP_

#include <exception>
#include "capd/intervals/MpInterval.h"
#include <fstream>

#ifdef __HAVE_MPFR__

namespace capd {
namespace intervals {

//////////////////////////////////////////////////////////////////////////
//  quadrant
///
/// returns the integer part of the division of x by Pi/2
/// the result is exact
//////////////////////////////////////////////////////////////////////////
MpInterval::BoundType quadrant(const MpInterval::BoundType &x) {
  int ok = 0;
  MpInterval::BoundType::PrecisionType defPrec = x.getDefaultPrecision(), prec =
      x.getPrecision(), precIncreaseRate = 64;
  MpInterval twoOverPi, tmp;
  MpInterval::BoundType quad = 0.0;

  if(!(x == 0)) {
    do {
      x.setDefaultPrecision(prec);
      twoOverPi = MpInterval(2.0) / MpInterval::pi();
      tmp = twoOverPi * x;
      ok = compare(floor(tmp.leftBound()), floor(tmp.rightBound()));

      if(ok != 0)
        prec = prec + precIncreaseRate;

    } while(ok != 0);

    quad = floor(tmp.leftBound());
    MpInterval::BoundType::setDefaultPrecision(defPrec);
  }
  return quad;
}

int modulo4(MpReal x) {
  while(x > 32000)
    x = x - MpReal(64000);
  while(x < -32000)
    x = x + MpReal(64000);
  //the revised codes by Qingdu Li
  int ir= toInt(x) % 4;
  ir = ir<0 ? ir+4 : ir;
  return ir;
}

template <>
MpInterval sin(const MpInterval& x) {
  MpInterval::BoundType quad_left, quad_right;
  MpInterval::BoundType left, right;

  int ql_mod4, qr_mod4;

  testNaN(x);

#ifdef _MPI_TEST_INF_
  if (isinf(x)) {
    /* the two endpoints are the same infinite */
    if ( compare(x.leftBound(), x.rightBound()) == 0)
    throw NaNException();

    return MpInterval(-1.0, 1.0);
  }
#endif  //_MPI_TEST_INF_

  // quad_left gives the quadrant where the left endpoint of b is
  // quad_left = floor(2 b->left / pi)
  // idem for quad_right and b->right

  quad_left = quadrant(x.leftBound());
  quad_right = quadrant(x.rightBound());

  if(quad_right - quad_left >= 4.0) {
    return MpInterval(-1, 1);
  } else {
    // there is less than one period in b
    // let us discuss according to the position (quadrant) of the endpoints of b

    // qr_mod4 gives the quadrant where the right endpoint of b is
    // qr_mod4 = floor(2 b->right / pi) mod 4
    qr_mod4 = modulo4(quad_right);

    // quad_left gives the quadrant where the left endpoint of b is
    // quad_left = floor(2 b->left / pi) mod 4
    ql_mod4 = modulo4(quad_left);

    switch(qr_mod4) {
      case 0:
        switch(ql_mod4) {
          case 0:
          case 3:
            MpReal::roundDown();
            left = sin(x.leftBound());
            MpReal::roundUp();
            right = sin(x.rightBound());
            break;

          case 1:
            MpReal::roundUp();
            left = sin(x.leftBound());
            right = sin(x.rightBound());
            if(right < left)
              right = left;
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;
          case 2:
            MpReal::roundUp();
            right = sin(x.rightBound());
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;
        } // gr_mod4 =  0:
        break;
      case 1:
        switch(ql_mod4) {
          case 0:
            MpReal::roundDown();
            left = sin(x.leftBound());
            right = sin(x.rightBound());
            if(right < left)
              left = right;
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            break;

          case 1:
            MpReal::roundDown();
            left = sin(x.rightBound());
            MpReal::roundUp();
            right = sin(x.leftBound());
            break;

          case 2:
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 3:
            MpReal::roundDown();
            left = sin(x.leftBound());
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            break;
        }// gr_mod4 =  1:
        break;
      case 2:
        switch(ql_mod4) {
          case 0:
            MpReal::roundDown();
            left = sin(x.rightBound());
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            break;

          case 1:
          case 2:
            MpReal::roundDown();
            left = sin(x.rightBound());
            MpReal::roundUp();
            right = sin(x.leftBound());
            break;

          case 3:
            MpReal::roundDown();
            left = sin(x.leftBound());
            right = sin(x.rightBound());
            if(right < left)
              left = right;
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            break;
        }// gr_mod4 =  2:
        break;
      case 3:
        switch(ql_mod4) {
          case 0:
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 1:
            MpReal::roundUp();
            right = sin(x.leftBound());
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 2:
            MpReal::roundUp();
            left = sin(x.leftBound());
            right = sin(x.rightBound());
            if(right < left)
              right = left;
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 3:
            MpReal::roundDown();
            left = sin(x.leftBound());
            MpReal::roundUp();
            right = sin(x.rightBound());
            break;

        } // gr_mod4 =  3:
        break;
    } // switch(gr_mod4)
  }
  return MpInterval(left, right);
} // sin


template <>
MpInterval cos(const MpInterval& x) {
  MpInterval::BoundType quad_left, quad_right;
  MpInterval::BoundType left, right;

  int ql_mod4, qr_mod4;

  testNaN(x);

#ifdef _MPI_TEST_INF_
  if (isinf(x))
  {
    // the two endpoints are the same infinite
    if ( compare(x.leftBound(), x.rightBound()) == 0)
    throw NaNException();

    return MpInterval(-1.0, 1.0);
  }
#endif //_MPI_TEST_INF_
  // quad_left gives the quadrant where the left endpoint of b is
  // quad_left = floor(2 b->left / pi)
  // idem for quad_right and b->right

  quad_left = quadrant(x.leftBound());
  quad_right = quadrant(x.rightBound());

  if(quad_right - quad_left >= 4.0) {
    return MpInterval(-1, 1);
  } else {
    // there is less than one period in b
    // let us discuss according to the position (quadrant) of the endpoints of b


    // qr_mod4 gives the quadrant where the right endpoint of b is
    // qr_mod4 = floor(2 b->right / pi) mod 4
    qr_mod4 = modulo4(quad_right); // Warning: It do not work for huge numbers

    // quad_left gives the quadrant where the left endpoint of b is
    // quad_left = floor(2 b->left / pi) mod 4
    ql_mod4 = modulo4(quad_left);

    switch(qr_mod4) {
      case 0:
        switch(ql_mod4) {

          case 0:
            MpReal::roundDown();
            left = cos(x.rightBound());
            MpReal::roundUp();
            right = cos(x.leftBound());
            break;

          case 1:
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 2:
            MpReal::roundDown();
            left = cos(x.leftBound());
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            break;

          case 3:
            MpReal::roundDown();
            left = cos(x.leftBound());
            right = cos(x.rightBound());
            if(right < left)
              left = right;
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            break;

        }
        break;
      case 1:
        switch(ql_mod4) {
          case 3:
            MpReal::roundDown();
            left = cos(x.rightBound());
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            break;

          case 0:
          case 1:
            MpReal::roundDown();
            left = cos(x.rightBound());
            MpReal::roundUp();
            right = cos(x.leftBound());
            break;

          case 2:
            MpReal::roundDown();
            left = cos(x.leftBound());
            right = cos(x.rightBound());
            if(right < left)
              left = right;
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            break;
        }
        break;
      case 2:
        switch(ql_mod4) {

          case 0:
            MpReal::roundUp();
            right = cos(x.leftBound());
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 1:
            MpReal::roundUp();
            left = cos(x.leftBound());
            right = cos(x.rightBound());
            if(right < left)
              right = left;
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 2:
            MpReal::roundDown();
            left = cos(x.leftBound());
            MpReal::roundUp();
            right = cos(x.rightBound());
            break;

          case 3:
            right = MpInterval::BoundType(1.0, MpInterval::BoundType::RoundUp);
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

        }
        break;

      case 3:
        switch(ql_mod4) {

          case 0:
            MpReal::roundUp();
            left = cos(x.leftBound());
            right = cos(x.rightBound());
            if(right < left)
              right = left;
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 1:
            MpReal::roundUp();
            right = cos(x.rightBound());
            left = MpInterval::BoundType(-1.0, MpInterval::BoundType::RoundDown);
            break;

          case 2:
          case 3:
            MpReal::roundDown();
            left = cos(x.leftBound());
            MpReal::roundUp();
            right = cos(x.rightBound());
            break;
        }
        break;
    }
  }
  return MpInterval(left, right);
} // cos


template <>
MpInterval tan(const MpInterval& x) {
  testNaN(x);

#ifdef _MPI_TEST_INF_
  if (isinf(x)) {
    /* the two endpoints are the same infinite */
    if ( compare(x.leftBound(), x.rightBound()) == 0)
    throw NaNException();

    return MpInterval(MpInterval::BoundType::negativeInfinity(), MpInterval::BoundType::positiveInfinity());
  }
#endif //_MPI_TEST_INF_

  MpInterval::BoundType quad_left = quadrant(x.leftBound()), quad_right =
      quadrant(x.rightBound());

  long int qr_mod2 = toInt(quad_right) % 2, // Warning: It do not work for huge numbers
      ql_mod2 = toInt(quad_left) % 2;

  /* if there is at least one period in b or if b contains a Pi/2 + k*Pi, */
  /* then a = ]-oo, +oo[ */
  if((quad_right - quad_left >= 2.0) || ((ql_mod2 == 0) && (qr_mod2 == 1)))
    return MpInterval(MpInterval::BoundType::negativeInfinity(),
        MpInterval::BoundType::positiveInfinity());

  /* within one period, tan is increasing */
  MpInterval::BoundType left, right;
  MpReal::roundDown();
  left = tan(x.leftBound());
  MpReal::roundUp();
  right = tan(x.rightBound());
  return MpInterval(left, right);
} //tan


template <>
MpInterval log(const MpInterval& x) {
  MpInterval::BoundType left, right;
  MpReal::roundDown();
  left = log(x.leftBound());
  MpReal::roundUp();
  right = log(x.rightBound());

  MpInterval res(left, right);
  testNaN(res);

  return res;
}

template <>
MpInterval exp(const MpInterval& x) {
  MpInterval::BoundType left, right;

  MpReal::roundDown();
  left = exp(x.leftBound());
  MpReal::roundUp();
  right = exp(x.rightBound());

  MpInterval res(left, right);
  testNaN(res);

  return res;
}

//-------- sqrt -----------------
template <>
MpInterval sqrt(const MpInterval & z) {
  MpInterval::BoundType left, right;

  if(z.leftBound() < 0.0) {
    throw IntervalError<MpReal> (
        "MpInterval Function sqrt(x) - domain error", z.leftBound(),
        z.rightBound());
  }
  MpReal::roundUp();
  right = sqrt(z.rightBound());

  MpReal::roundDown();
  left = sqrt(z.leftBound());

  return MpInterval(left, right);
}//-------------------------------


template <>
MpInterval power(const MpInterval& value, /*long*/int e)
//   value^{exponent}
{

  int sign = e<0 ? 0 : 1;
  unsigned long int exponent = e < 0 ? -e : e;

  MpInterval::BoundType l = value.leftBound(),
                        r = value.rightBound();

  /* if 'exponent' is even, then we need to correct the ends of interval -
   only absolute values matter*/
  if(exponent % 2 == 0) {
    l = abs(l);
    r = abs(r);
    if(l > r) {
      MpInterval::BoundType t = r;
      r = l;
      l = t;
    }
    if(value.contains(0.0))
      l = 0.0;
  }
  //MpReal::roundUp();
    r = r.pow(exponent, MpInterval::BoundType::RoundUp);
  //MpReal::roundDown();
    l = l.pow(exponent,MpInterval::BoundType::RoundDown);

  MpInterval out(l, r);

  if(sign == 0){ // when an exponent is negative
    out = MpInterval(1.0) / out;
  }

  return out;
}//--------------------------------------------------------------------

}
} // end of namespace capd::intervals

#endif  // __HAVE_MPFR__
#endif  // _MP_INTERVAL_FUN_
/// @}

