//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file MpReal_Base.hpp
///
/// @author Tomasz Kapela   @date 2010-03-15
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_MULTIPREC_MPREAL_BASE_HPP_
#define _CAPD_MULTIPREC_MPREAL_BASE_HPP_

namespace capd {
namespace multiPrec {

//--------------------------------------------------------------
//
// Constructors and destructors
//
//--------------------------------------------------------------

inline MpReal::MpReal() {
  mpfr_init2(mpfr_rep, getDefaultPrecision());
  mpfr_set_d(mpfr_rep, 0.0, MpReal::RoundToZero);
}

inline MpReal::MpReal(double d, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  mpfr_set_d(mpfr_rep, d, rnd);
}

inline MpReal::MpReal(long double d, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  mpfr_set_ld(mpfr_rep, d, rnd);
}

inline MpReal::MpReal(int i, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  mpfr_set_si(mpfr_rep, (long) (i), rnd);
}

inline MpReal::MpReal(unsigned int i, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  mpfr_set_ui(mpfr_rep, (unsigned long int) i, rnd);
}

inline MpReal::MpReal(long int i, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  mpfr_set_si(mpfr_rep, i, rnd);
}

inline MpReal::MpReal(unsigned long int i, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  mpfr_set_ui(mpfr_rep, i, rnd);
}

inline MpReal::MpReal(std::string s, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  if(mpfr_set_str(mpfr_rep, const_cast<char *> (s.c_str()), 10, rnd)) {
    throw(std::runtime_error((std::string(
        "Problem in MpReal when initializing with string : ") + s).c_str()));
  }
}
inline MpReal::MpReal(const char * s, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  if(mpfr_set_str(mpfr_rep, s, 10, rnd)) {
    throw(std::runtime_error((std::string(
        "Problem in MpReal when initializing with string : ") + s).c_str()));
  }
}

inline MpReal::MpReal(const MpReal& r) {
  mpfr_init2(mpfr_rep, r.getPrecision());
  mpfr_set(mpfr_rep, r.mpfr_rep, MpReal::getDefaultRndMode());
}

inline MpReal::~MpReal() {
  mpfr_clear(mpfr_rep);
}

//--------------------------------------------------------------
//
// Assignment and physical copy
//
//--------------------------------------------------------------

// Assignment is a logical copy
inline MpReal& MpReal::operator =(const MpReal& r) {
  if(this != &r) {
    if(this->getPrecision() != r.getPrecision()) {
      setPrecision(r.getPrecision());
    }
    mpfr_set(mpfr_rep, r.mpfr_rep, getDefaultRndMode());
  }
  return *this;
}

//--------------------------------------------------------------
//
// Precision and rounding: consultation, modification
//
//--------------------------------------------------------------

inline void MpReal::setPrecision(MpReal::PrecisionType newprec) {
  mpfr_prec_round(mpfr_rep, newprec, MpReal::getDefaultRndMode());
}

inline void MpReal::setDefaultPrecision(MpReal::PrecisionType newprec) {
  mpfr_set_default_prec(newprec);
}

inline MpReal::PrecisionType MpReal::getDefaultPrecision() {
  return mpfr_get_default_prec();
}

inline MpReal::PrecisionType MpReal::getPrecision() const {
  return mpfr_get_prec(mpfr_rep);
}

inline void MpReal::setDefaultRndMode(RoundingMode newrndmode) {
  mpfr_set_default_rounding_mode(newrndmode);
}

inline MpReal::RoundingMode MpReal::getDefaultRndMode() {
  return RoundingMode(mpfr_get_default_rounding_mode());
}

inline void MpReal::roundUp() {
  setDefaultRndMode(RoundUp);
}
inline void MpReal::roundDown() {
  setDefaultRndMode(RoundDown);
}

inline void MpReal::roundNearest() {
  setDefaultRndMode(RoundNearest);
}

inline void MpReal::roundCut() {
  setDefaultRndMode(RoundToZero);
}

//--------------------------------------------------------------
//
// Constants: Pi, log(2) and Euler constant
//
//--------------------------------------------------------------
//
inline MpReal MpReal::pi(RoundingMode rnd, PrecisionType prec) {
  MpReal res(0, MpReal::getDefaultRndMode(), prec);
  mpfr_const_pi(res.mpfr_rep, rnd);
  return res;
}

inline MpReal MpReal::log2(RoundingMode rnd, PrecisionType prec) {
  MpReal res(0, MpReal::getDefaultRndMode(), prec);
  mpfr_const_log2(res.mpfr_rep, rnd);
  return res;
}

inline MpReal MpReal::euler(RoundingMode rnd, PrecisionType prec) {
  MpReal res(0, MpReal::getDefaultRndMode(), prec);
  mpfr_const_euler(res.mpfr_rep, rnd);
  return res;
}

inline MpReal MpReal::positiveInfinity(PrecisionType prec) {
  MpReal res(0, MpReal::getDefaultRndMode(), prec);
  mpfr_set_inf(res.mpfr_rep, 1);
  return res;

}

inline MpReal MpReal::negativeInfinity(PrecisionType prec) {
  MpReal res(0, MpReal::getDefaultRndMode(), prec);
  mpfr_set_inf(res.mpfr_rep, -1);
  return res;
}

}
} // end of namespace capd::multiPrec

#endif // _CAPD_MULTIPREC_MPREAL_BASE_HPP_
