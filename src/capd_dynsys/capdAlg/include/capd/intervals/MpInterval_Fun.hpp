/////////////////////////////////////////////////////////////////////////////
/// @file MpInterval_Fun.hpp
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#ifndef _CAPD_INTERVAL_MPINTERVAL_FUN_H_
#define _CAPD_INTERVAL_MPINTERVAL_FUN_H_

#include <exception>
#include "capd/intervals/MpInterval.h"
#include "capd/intervals/MpIntervalSettings.h"

class NaNException : public std::exception {
  const char * what() const throw () {
    return "Not a number. ";
  }
};

#ifdef __HAVE_MPFR__

namespace capd {
namespace intervals {


inline void testNaN(const MpInterval & x) {
#ifdef __MPI_TEST_NAN__
  if(isNaN(x.leftBound()) || isNaN(x.rightBound())))
  throw NaNException();
#endif  // __MPI_TEST_NAN__
}

template <>
MpInterval sin(const MpInterval& x);

template <>
MpInterval cos(const MpInterval& x);

template <>
MpInterval tan(const MpInterval& x);

template <>
MpInterval log(const MpInterval& x);

template <>
MpInterval exp(const MpInterval& x);

//-------- sqrt -----------------
template <>
MpInterval sqrt(const MpInterval & z);

template <>
inline MpInterval power(const MpInterval &a, const MpInterval &b) {
  if(a.leftBound() < 0) {
    throw std::range_error(
        "power(A, B): interval A must be greater than zero\n");
  }
  return exp(b * log(a));
}

template <>
MpInterval power(const MpInterval& value, /*long*/int exponent);

template <>
inline MpInterval MpInterval::pi() {
  BoundType::PrecisionType prec = BoundType::getDefaultPrecision();
  return MpInterval(
      BoundType::pi(BoundType::RoundDown, prec),
      BoundType::pi(BoundType::RoundUp, prec)
  );
}

/*
 //  So far not defined in Interval template
 //
 template<>
 MpInterval MpInterval::log2()
 {

 capd::multiPrec::PrecisionType   prec = BoundType::getDefaultPrecision();
 return MpInterval(BoundType::Log2(capd::multiPrec::RoundDown, prec), BoundType::Log2(capd::multiPrec::RoundUp, prec));
 }
 */

template <>
inline MpInterval MpInterval::euler() {
  BoundType::PrecisionType prec = BoundType::getDefaultPrecision();
  return MpInterval(
      BoundType::euler(BoundType::RoundDown, prec),
      BoundType::euler(BoundType::RoundUp, prec)
  );
}

Interval<MpReal>::BoundType quadrant(const Interval<MpReal>::BoundType &x);
int modulo4(MpReal x);

}} // end of namespace capd::intervals

#endif  // __HAVE_MPFR__
#endif // _CAPD_INTERVAL_MPINTERVALFUN_H_ 

