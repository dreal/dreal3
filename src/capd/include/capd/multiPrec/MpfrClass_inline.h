/////////////////////////////////////////////////////////////////////////////
/// @addtogroup multiPrec
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file MpfrClass_inline.h
///
/// inline function for class MpfrClass
///
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2009
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


#ifndef _CAPD_MULTIPREC_MPFRCLASSINLINE_H_
#define _CAPD_MULTIPREC_MPFRCLASSINLINE_H_

#include "capd/multiPrec/MpSetting.h"

#ifdef __HAVE_MPFR__

namespace capd {
namespace multiPrec {

//--------------------------------------------------------------
//
// Precision and rounding: consultation, modification
//
//--------------------------------------------------------------

inline void MpfrClass::setDefaultPrecision(MpfrClass::PrecisionType newprec) {
  mpfr_set_default_prec(newprec);
}

inline const MpfrClass::PrecisionType MpfrClass::getDefaultPrecision() {
  return mpfr_get_default_prec();
}

inline MpfrClass::PrecisionType MpfrClass::getPrecision() const {
  return mpfr_get_prec(mpfr_rep);
}

inline void MpfrClass::setDefaultRndMode(RoundingMode newrndmode) {
  mpfr_set_default_rounding_mode(newrndmode);
}

inline const RoundingMode MpfrClass::getDefaultRndMode() {
  return RoundingMode(mpfr_get_default_rounding_mode());
}

inline void MpfrClass::roundUp() {
  setDefaultRndMode(RoundUp);
}
inline void MpfrClass::roundDown() {
  setDefaultRndMode(RoundDown);
}

inline void MpfrClass::roundNearest() {
  setDefaultRndMode(RoundNearest);
}

inline void MpfrClass::roundCut() {
  setDefaultRndMode(RoundToZero);
}

//--------------------------------------------------------------
//
// Comparisons
//
//--------------------------------------------------------------

/////////////////////////////////////////////////////////////////
// compare
///
/// Compares two numbers
///
/// @param[in] r1,r2  numbers to be compared
///
/// @returns  negative number if r1 < r2
///           0 if r1 == r2
///           positive number if r1 > r2
///
//////////////////////////////////////////////////////////////////
inline int compare(const MpfrClass& r1, const MpfrClass& r2) {
  return mpfr_cmp(r1.mpfr_rep, r2.mpfr_rep);
}

inline int compare(const MpfrClass& r1, const double r2) {
  return mpfr_cmp_d(r1.mpfr_rep, r2);
}

inline int compare(const MpfrClass& r1, const int r2) {
  return mpfr_cmp_si(r1.mpfr_rep, long(r2));
}

inline int compare(const MpfrClass& r1, const unsigned int r2) {
  return mpfr_cmp_ui(r1.mpfr_rep, (unsigned long) r2);
}

inline int compare(const MpfrClass& r1, const long int r2) {
  return mpfr_cmp_si(r1.mpfr_rep, r2);
}

inline int compare(const MpfrClass& r1, const unsigned long r2) {
  return mpfr_cmp_ui(r1.mpfr_rep, r2);
}

inline bool operator ==(const MpfrClass& r1, const MpfrClass& r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const double r1, const MpfrClass& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const int r1, const MpfrClass& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const unsigned int r1, const MpfrClass& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const unsigned long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const MpfrClass& r1, const double r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const MpfrClass& r1, const int r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const MpfrClass& r1, const unsigned int r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const MpfrClass& r1, const long int r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const MpfrClass& r1, const unsigned long int r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator !=(const MpfrClass& r1, const MpfrClass& r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const double r1, const MpfrClass& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const int r1, const MpfrClass& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const unsigned int r1, const MpfrClass& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const unsigned long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const MpfrClass& r1, const double r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const MpfrClass& r1, const int r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const MpfrClass& r1, const unsigned int r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const MpfrClass& r1, const long int r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const MpfrClass& r1, const unsigned long int r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator <(const MpfrClass& r1, const MpfrClass& r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const double r1, const MpfrClass& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const int r1, const MpfrClass& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const unsigned int r1, const MpfrClass& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const unsigned long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const MpfrClass& r1, const double r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const MpfrClass& r1, const int r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const MpfrClass& r1, const unsigned int r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const MpfrClass& r1, const long int r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const MpfrClass& r1, const unsigned long int r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <=(const MpfrClass& r1, const MpfrClass& r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const double r1, const MpfrClass& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const int r1, const MpfrClass& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const unsigned int r1, const MpfrClass& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const unsigned long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const MpfrClass& r1, const double r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const MpfrClass& r1, const int r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const MpfrClass& r1, const unsigned int r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const MpfrClass& r1, const long int r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const MpfrClass& r1, const unsigned long int r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator >(const MpfrClass& r1, const MpfrClass& r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const double r1, const MpfrClass& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const int r1, const MpfrClass& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const unsigned int r1, const MpfrClass& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const unsigned long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const MpfrClass& r1, const double r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const MpfrClass& r1, const int r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const MpfrClass& r1, const unsigned int r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const MpfrClass& r1, const long int r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const MpfrClass& r1, const unsigned long int r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >=(const MpfrClass& r1, const MpfrClass& r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const double r1, const MpfrClass& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const int r1, const MpfrClass& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const unsigned int r1, const MpfrClass& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const unsigned long int r1, const MpfrClass& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const MpfrClass& r1, const double r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const MpfrClass& r1, const int r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const MpfrClass& r1, const unsigned int r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const MpfrClass& r1, const long int r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const MpfrClass& r1, const unsigned long int r2) {
  return (compare(r1, r2) >= 0);
}

// To be checked: IEEE recommendation when one operand is an exception
inline MpfrClass min(const MpfrClass& a, const MpfrClass& b) {
  return (a <= b) ? a : b;
}

inline MpfrClass max(const MpfrClass& a, const MpfrClass& b) {
  return (a >= b) ? a : b;
}

//---------------------------------------------------------------------
//
//  Arithmetic operators
//
//---------------------------------------------------------------------

inline MpfrClass operator +(const double a, const MpfrClass& b) {
  return b + a;
}

inline MpfrClass operator +(const int a, const MpfrClass& b) {
  return b + a;
}

inline MpfrClass operator +(const unsigned int a, const MpfrClass& b) {
  return b + a;
}

inline MpfrClass operator +(const long int a, const MpfrClass& b) {
  return b + a;
}

inline MpfrClass operator +(const unsigned long int a, const MpfrClass& b) {
  return b + a;
}

inline MpfrClass operator +(const mpz_srcptr a, const MpfrClass& b) {
  return b + a;
}

inline MpfrClass operator +(const mpq_srcptr a, const MpfrClass& b) {
  return b + a;
}

//----------------------------------------------------------------------
//
//   Functions
//
//----------------------------------------------------------------------

inline MpfrClass abs(const MpfrClass& r, RoundingMode rnd) {
  if(r >= 0)
    return r + 0; // changes the precision of r
  // if getDefaultPrecision() != prec of r
  else
    return -r;
}

inline MpfrClass agm(const MpfrClass& r1, const MpfrClass& r2, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_agm(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
      rnd);
  return res;
}

inline MpfrClass sqrt(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  // NaN handled by MPFR in case r < 0
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_sqrt(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass exp(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_exp(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass expm1(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_expm1(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass log(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  // NaN handled by MPFR in case r < 0
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_log(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass log2(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  // NaN handled by MPFR in case r < 0
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_log2(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass log10(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  // NaN handled by MPFR in case r < 0
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_log10(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass log1p(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  // NaN handled by MPFR in case r < 0
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_log1p(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass sin(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_sin(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass cos(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_cos(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

// new functions 10/04/03

inline MpfrClass tan(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_tan(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass acos(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_acos(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass asin(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_asin(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass atan(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_atan(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass cosh(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_cosh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass sinh(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_sinh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass tanh(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_tanh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass asinh(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_asinh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass acosh(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_acosh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass atanh(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_atanh(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass MpfrClass::pow(const unsigned long int e, RoundingMode rnd) const {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_pow_ui(res.mpfr_rep, mpfr_rep, e, rnd);
  return res;
}

inline MpfrClass MpfrClass::pow(const long int e, RoundingMode rnd) const {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_pow_si(res.mpfr_rep, mpfr_rep, e, rnd);
  return res;
}

inline MpfrClass MpfrClass::pow(const MpfrClass& e, RoundingMode rnd) const {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_pow(res.mpfr_rep, mpfr_rep, e.mpfr_rep, rnd);
  return res;
}

inline MpfrClass cbrt(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_cbrt(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass exp2(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_exp2(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass gamma(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_gamma(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass erf(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_erf(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

inline MpfrClass factorial(const unsigned long int n, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_fac_ui(res.mpfr_rep, n, rnd);
  return res;
}

inline MpfrClass hypot(const MpfrClass& r1, const MpfrClass& r2,
    RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_hypot(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
      rnd);
  return res;
}

inline MpfrClass zeta(const MpfrClass& r, RoundingMode rnd) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_zeta(res.mpfr_rep, r.mpfr_rep, rnd);
  return res;
}

// end new functions
//
//

inline MpfrClass round(const MpfrClass& r) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_round(res.mpfr_rep, r.mpfr_rep);
  return res;
}

inline MpfrClass floor(const MpfrClass& r) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_floor(res.mpfr_rep, r.mpfr_rep);
  return res;
}

inline MpfrClass trunc(const MpfrClass& r) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_trunc(res.mpfr_rep, r.mpfr_rep);
  return res;
}

inline MpfrClass ceil(const MpfrClass& r) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_ceil(res.mpfr_rep, r.mpfr_rep);
  return res;
}

inline MpfrClass frac(const MpfrClass& r) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_frac(res.mpfr_rep, r.mpfr_rep,
      MpfrClass::getDefaultRndMode());
  return res;
}

inline long int toInt(const MpfrClass& r, RoundingMode rnd) {
  return mpfr_get_si(r.mpfr_rep, rnd);
}

inline unsigned long int toUInt(const MpfrClass& r, RoundingMode rnd) {
  return mpfr_get_ui(r.mpfr_rep, rnd);
}

inline double toDouble(const MpfrClass& r, RoundingMode rnd) {
  return mpfr_get_d(r.mpfr_rep, rnd);
}

inline long double toLDouble(const MpfrClass& r, RoundingMode rnd) {
  return mpfr_get_ld(r.mpfr_rep, rnd);
}

inline MpfrClass relDiff(const MpfrClass& r1, const MpfrClass& r2,
    RoundingMode rnd) {
  MpfrClass res;

  mpfr_reldiff(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, rnd);
  return res;
}

inline MpfrClass nextAbove(const MpfrClass& r) {
  MpfrClass res;

  res.copy(r);
  mpfr_nextabove(res.mpfr_rep);
  return res;
}

inline MpfrClass nextBelow(const MpfrClass& r) {
  MpfrClass res;

  res.copy(r);
  mpfr_nextbelow(res.mpfr_rep);
  return res;
}

inline MpfrClass nextToward(const MpfrClass& r, const MpfrClass& dir) {
  MpfrClass res;

  res.copy(r);
  mpfr_nexttoward(res.mpfr_rep, dir.mpfr_rep);
  return res;
}

}
} // end of namespace capd::multiPrec


#endif  // __HAVE_MPFR__
#endif  // MPFRCLASSINLINE
/// @}
