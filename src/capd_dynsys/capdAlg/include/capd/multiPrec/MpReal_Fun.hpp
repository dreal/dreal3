//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file MpReal_Fun.hpp
///
/// @author Tomasz Kapela   @date 2010-03-15
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_MULTIPREC_MPREAL_FUN_HPP_
#define _CAPD_MULTIPREC_MPREAL_FUN_HPP_

namespace capd {
namespace multiPrec {
//----------------------------------------------------------------------
//
//   Functions
//
//----------------------------------------------------------------------

inline MpReal abs(const MpReal& r, MpReal::RoundingMode rnd) {
  if(r >= 0)
    return r; // changes the precision of r
  // if getDefaultPrecision() != prec of r
  else
    return -r;
}

inline MpReal agm(const MpReal& r1, const MpReal& r2, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_agm(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, rnd);
  return res;
}

inline MpReal sqr(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  // NaN handled by MPFR in case r < 0
  mpfr_sqr(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal sqrt(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  // NaN handled by MPFR in case r < 0
  mpfr_sqrt(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal exp(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_exp(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal expm1(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_expm1(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal log(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_log(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal log2(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_log2(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal log10(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_log10(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal log1p(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_log1p(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal sin(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_sin(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal cos(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_cos(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

// new functions 10/04/03

inline MpReal tan(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_tan(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal acos(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_acos(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal asin(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_asin(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal atan(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_atan(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal cosh(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_cosh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal sinh(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_sinh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal tanh(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_tanh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal asinh(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_asinh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal acosh(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_acosh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal atanh(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_atanh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal MpReal::pow(const unsigned long int e, MpReal::RoundingMode rnd) const {
  MpReal res;
  mpfr_pow_ui(res.mpfr_rep, mpfr_rep, e, rnd);
  return res;
}

inline MpReal MpReal::pow(const long int e, MpReal::RoundingMode rnd) const {
  MpReal res;
  mpfr_pow_si(res.mpfr_rep, mpfr_rep, e, rnd);
  return res;
}

inline MpReal MpReal::pow(const MpReal& e, MpReal::RoundingMode rnd) const {
  MpReal res;
  mpfr_pow(res.mpfr_rep, mpfr_rep, e.mpfr_rep, rnd);
  return res;
}
inline MpReal pow(const MpReal & x, const MpReal &e) {
  return x.pow(e, MpReal::getDefaultRndMode());
}
inline MpReal pow(const MpReal & x, const long int e) {
  return x.pow(e, MpReal::getDefaultRndMode());
}
inline MpReal power(const MpReal & x, const MpReal &e) {
  return x.pow(e, MpReal::getDefaultRndMode());
}
inline MpReal power(const MpReal & x, const long int e) {
  return x.pow(e, MpReal::getDefaultRndMode());
}

inline MpReal cbrt(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_cbrt(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal exp2(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_exp2(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal gamma(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_gamma(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpReal erf(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_erf(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

//inline MpReal factorial(const unsigned long int n, MpReal::RoundingMode rnd) {
//  MpReal res;
//  mpfr_fac_ui(res.mpfr_rep, n, rnd);
//  return res;
//}

inline MpReal hypot(const MpReal& r1, const MpReal& r2,
    MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_hypot(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, rnd);
  return res;
}

inline MpReal zeta(const MpReal& r, MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_zeta(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}
//--------------------------------------------------------------
//
// Mathematical and miscellaneous functions
//
//--------------------------------------------------------------
// NaN of infinity handled by MPFR
// => no test on the value (sign...) of the operand
//void MpReal::random(PrecisionType prec) // member to avoid conflict with GMP random
//{
//  if(nbref->decr() <= 0) // the memory can be reused
//  {
//    nbref->refvalue() = 1;
//    mpfr_set_prec(mpfr_rep, prec);
//  } else // the previous value must be preserved
//  {
//    mpfr_init2(mpfr_rep, prec);
//    nbref = new RefCounter(1);
//    inexact = new InexactFlag();
//  }
//  mpfr_random(mpfr_rep);
//  inexact->refvalue() = EXACT_FLAG;
//}

inline void sin_cos(MpReal& res_sin, MpReal& res_cos, const MpReal& r,
    MpReal::RoundingMode rnd) {
  mpfr_sin_cos(res_sin.mpfr_rep, res_cos.mpfr_rep, r.mpfr_rep, rnd);
}

inline MpReal round(const MpReal& r) {
  MpReal res;
  mpfr_round(res.mpfr_rep, r.mpfr_rep);
  return res;
}

inline MpReal floor(const MpReal& r) {
  MpReal res;
  mpfr_floor(res.mpfr_rep, r.mpfr_rep);
  return res;
}

inline MpReal trunc(const MpReal& r) {
  MpReal res;
  mpfr_trunc(res.mpfr_rep, r.mpfr_rep);
  return res;
}

inline MpReal ceil(const MpReal& r) {
  MpReal res;
  mpfr_ceil(res.mpfr_rep, r.mpfr_rep);
  return res;
}

inline MpReal frac(const MpReal& r) {
  MpReal res;
  mpfr_frac(res.mpfr_rep, r.mpfr_rep, MpReal::getDefaultRndMode());
  return res;
}

inline long int toInt(const MpReal& r, MpReal::RoundingMode rnd) {
  return mpfr_get_si(r.mpfr_rep, rnd);
}

inline long int toLongInt(const MpReal& r, MpReal::RoundingMode rnd) {
  return mpfr_get_si(r.mpfr_rep, rnd);
}

inline unsigned long int toUInt(const MpReal& r, MpReal::RoundingMode rnd) {
  return mpfr_get_ui(r.mpfr_rep, rnd);
}

inline double toDouble(const MpReal& r, MpReal::RoundingMode rnd) {
  return mpfr_get_d(r.mpfr_rep, rnd);
}

inline long double toLongDouble(const MpReal& r, MpReal::RoundingMode rnd) {
  return mpfr_get_ld(r.mpfr_rep, rnd);
}

inline MpReal relDiff(const MpReal& r1, const MpReal& r2,
    MpReal::RoundingMode rnd) {
  MpReal res;
  mpfr_reldiff(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, rnd);
  return res;
}

inline MpReal nextAbove(const MpReal & r) {
  MpReal res(r);
  mpfr_nextabove(res.mpfr_rep);
  return res;
}

inline MpReal nextBelow(const MpReal& r) {
  MpReal res(r);
  mpfr_nextbelow(res.mpfr_rep);
  return res;
}

inline MpReal nextToward(const MpReal& r, const MpReal& dir) {
  MpReal res(r);
  mpfr_nexttoward(res.mpfr_rep, dir.mpfr_rep);
  return res;
}

inline const MpReal & nonnegativePart(const MpReal & x) {
  if(x >= 0)
    return x;
  else
    throw std::runtime_error(" MpReal : nonnegative part is empty");
}

inline MpReal right(const MpReal& x) {
  return x;
}

inline MpReal left(const MpReal& x) {
  return x;
}

inline MpReal mid(const MpReal& x) {
  return x;
}
// end new functions
//
//
}
} // end of namespace capd::multiPrec

#endif // _CAPD_MULTIPREC_MPREAL_FUN_HPP_
