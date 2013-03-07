//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file MpReal_Op.hpp
///
/// @author Tomasz Kapela   @date 2010-03-15
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_MULTIPREC_MPREAL_OP_HPP_
#define _CAPD_MULTIPREC_MPREAL_OP_HPP_

namespace capd {
namespace multiPrec {

//--------------------------------------------------------------
//
// Arithmetic operations
// Pb with operators: it is impossible to stick to MPFR philosophy
// which states that the result of an arithmetic op. is computed
// with the precision of the result, since the result is not yet known.
//
//--------------------------------------------------------------

// Addition-----------------------------------------------------

inline MpReal operator +(const MpReal& a, const MpReal& b) {
  if(isZero(b)) {
    return a;
  } else if(isZero(a)) {
    return b;
  } else {
    MpReal res;
    mpfr_add(res.mpfr_rep, a.mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
    return res;
  }
}

inline MpReal& MpReal::operator +=(const MpReal& b) {
  if(isZero(b))
    return *this;
  if(!isZero(*this)) {
    mpfr_add(mpfr_rep, mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
  } else {
    *this = b;
  }
  return *this;
}

inline void MpReal::add(MpReal& res, const MpReal& r1, const MpReal& r2,
    RoundingMode rnd)
// This function is the one where the philosophy of MPFR is preserved:
// in this function the result is computed with the precision of the result.
{
  if(!isZero(r1)) {
    if(!isZero(r2)) {
      mpfr_add(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, rnd);
    } else {
      mpfr_set(res.mpfr_rep, r1.mpfr_rep, rnd);
    }
  } else {
    mpfr_set(res.mpfr_rep, r2.mpfr_rep, rnd);
  }
}

// Subtraction --------------------------------------------------------
inline MpReal operator -(const MpReal& a, const MpReal& b) {
  MpReal res;
  mpfr_sub(res.mpfr_rep, a.mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
  return res;
}

inline MpReal& MpReal::operator -=(const MpReal& b) {
  if(!isZero(b)) {
    if(isZero(*this)) {
      mpfr_neg(mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
    } else {
      mpfr_sub(mpfr_rep, mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
    }
  }
  return *this;
}

inline void MpReal::neg(MpReal& res, const MpReal& r, RoundingMode rnd) {
  mpfr_neg(res.mpfr_rep, r.mpfr_rep, rnd);
}

inline MpReal MpReal::operator -() const {
  MpReal res;
  MpReal::neg(res, *this, MpReal::getDefaultRndMode());
  return res;
}

inline void MpReal::sub(MpReal& res, const MpReal& r1, const MpReal& r2,
    RoundingMode rnd) {
  mpfr_sub(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, rnd);
}

// Multiplication-----------------------------------------------
inline MpReal operator *(const MpReal & a, const MpReal & b) {
  MpReal res;
  mpfr_mul(res.mpfr_rep, a.mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
  return res;
}

inline MpReal& MpReal::operator *=(const MpReal& b) {
  mpfr_mul(mpfr_rep, mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
  return *this;
}

inline void MpReal::mul(MpReal& res, const MpReal& r1, const MpReal& r2,
    RoundingMode rnd) {
  mpfr_mul(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, rnd);
}

// Division-----------------------------------------------------
inline MpReal operator /(const MpReal & a, const MpReal& b) {
  MpReal res;
  mpfr_div(res.mpfr_rep, a.mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
  return res;
}

inline MpReal& MpReal::operator /=(const MpReal& b) {
  mpfr_div(mpfr_rep, mpfr_rep, b.mpfr_rep, MpReal::getDefaultRndMode());
  return *this;
}

inline void MpReal::div(MpReal& res, const MpReal& r1, const MpReal& r2,
    RoundingMode rnd) {
  mpfr_div(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, rnd);
}

/// res = r1*r2+r3
inline void MpReal::fma(MpReal& res, const MpReal& r1, const MpReal& r2,
    const MpReal& r3, RoundingMode rnd) {
  mpfr_fma(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep, r3.mpfr_rep, rnd);
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
inline int compare(const MpReal& r1, const MpReal& r2) {
  return mpfr_cmp(r1.mpfr_rep, r2.mpfr_rep);
}

inline int compare(const MpReal& r1, const double r2) {
  return mpfr_cmp_d(r1.mpfr_rep, r2);
}

inline int compare(const MpReal& r1, const int r2) {
  return mpfr_cmp_si(r1.mpfr_rep, long(r2));
}

inline int compare(const MpReal& r1, const unsigned int r2) {
  return mpfr_cmp_ui(r1.mpfr_rep, (unsigned long) r2);
}

inline int compare(const MpReal& r1, const long int r2) {
  return mpfr_cmp_si(r1.mpfr_rep, r2);
}

inline int compare(const MpReal& r1, const unsigned long r2) {
  return mpfr_cmp_ui(r1.mpfr_rep, r2);
}

inline bool operator ==(const MpReal& r1, const MpReal& r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const double r1, const MpReal& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const int r1, const MpReal& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const unsigned int r1, const MpReal& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const long int r1, const MpReal& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const unsigned long int r1, const MpReal& r2) {
  return (compare(r2, r1) == 0);
}

inline bool operator ==(const MpReal& r1, const double r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const MpReal& r1, const int r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const MpReal& r1, const unsigned int r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const MpReal& r1, const long int r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator ==(const MpReal& r1, const unsigned long int r2) {
  return (compare(r1, r2) == 0);
}

inline bool operator !=(const MpReal& r1, const MpReal& r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const double r1, const MpReal& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const int r1, const MpReal& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const unsigned int r1, const MpReal& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const long int r1, const MpReal& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const unsigned long int r1, const MpReal& r2) {
  return (compare(r2, r1) != 0);
}

inline bool operator !=(const MpReal& r1, const double r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const MpReal& r1, const int r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const MpReal& r1, const unsigned int r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const MpReal& r1, const long int r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator !=(const MpReal& r1, const unsigned long int r2) {
  return (compare(r1, r2) != 0);
}

inline bool operator <(const MpReal& r1, const MpReal& r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const double r1, const MpReal& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const int r1, const MpReal& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const unsigned int r1, const MpReal& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const long int r1, const MpReal& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const unsigned long int r1, const MpReal& r2) {
  return (compare(r2, r1) > 0);
}

inline bool operator <(const MpReal& r1, const double r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const MpReal& r1, const int r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const MpReal& r1, const unsigned int r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const MpReal& r1, const long int r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <(const MpReal& r1, const unsigned long int r2) {
  return (compare(r1, r2) < 0);
}

inline bool operator <=(const MpReal& r1, const MpReal& r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const double r1, const MpReal& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const int r1, const MpReal& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const unsigned int r1, const MpReal& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const long int r1, const MpReal& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const unsigned long int r1, const MpReal& r2) {
  return (compare(r2, r1) >= 0);
}

inline bool operator <=(const MpReal& r1, const double r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const MpReal& r1, const int r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const MpReal& r1, const unsigned int r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const MpReal& r1, const long int r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator <=(const MpReal& r1, const unsigned long int r2) {
  return (compare(r1, r2) <= 0);
}

inline bool operator >(const MpReal& r1, const MpReal& r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const double r1, const MpReal& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const int r1, const MpReal& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const unsigned int r1, const MpReal& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const long int r1, const MpReal& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const unsigned long int r1, const MpReal& r2) {
  return (compare(r2, r1) < 0);
}

inline bool operator >(const MpReal& r1, const double r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const MpReal& r1, const int r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const MpReal& r1, const unsigned int r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const MpReal& r1, const long int r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >(const MpReal& r1, const unsigned long int r2) {
  return (compare(r1, r2) > 0);
}

inline bool operator >=(const MpReal& r1, const MpReal& r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const double r1, const MpReal& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const int r1, const MpReal& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const unsigned int r1, const MpReal& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const long int r1, const MpReal& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const unsigned long int r1, const MpReal& r2) {
  return (compare(r2, r1) <= 0);
}

inline bool operator >=(const MpReal& r1, const double r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const MpReal& r1, const int r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const MpReal& r1, const unsigned int r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const MpReal& r1, const long int r2) {
  return (compare(r1, r2) >= 0);
}

inline bool operator >=(const MpReal& r1, const unsigned long int r2) {
  return (compare(r1, r2) >= 0);
}

// To be checked: IEEE recommendation when one operand is an exception
inline const MpReal & min(const MpReal& a, const MpReal& b) {
  return (a <= b) ? a : b;
}

inline const MpReal & max(const MpReal& a, const MpReal& b) {
  return (a >= b) ? a : b;
}

//--------------------------------------------------------------
//
// Input Output
//
//--------------------------------------------------------------

// Outputs the value on the stream o in base 'base' with 'nb_digits'
// with rounding mode rnd
inline std::ostream& MpReal::put(std::ostream& o, RoundingMode rnd,
    PrecisionType prec, int base, int nb_digits) const {

  bool neg = (sign(*this) < 0);

  if(isInf(*this)) {
    if(neg)
      o << "-";
    o << "Inf ";
    return o;
  }
  if(isNaN(*this)) {
    o << "NaN";
    return o;
  }
  if(isZero(*this)) {
    if(neg)
      o << "-";
    o << "0 ";
    return o;
  }

  // Based on mpfr_get_str to create the string
  // Output done in another way (digit . fraction x E...).
  char *s, *fraction, first_digit;
  mp_exp_t e;
  s = mpfr_get_str(NULL, &e, base, nb_digits, mpfr_rep, rnd);
  // to print the floating point
  if(s[0] == '-') {
    o << s[0];
    first_digit = s[1];
    fraction = &s[2];
  } else {
    first_digit = s[0];
    fraction = &s[1];
  }
  o << first_digit << "." << fraction;
  mpfr_free_str(s);
  if(--e) {
    o << "e" << e;
  }
  o << " ";
  return o;
}

inline void MpReal::get(const std::string & str,
   		RoundingMode rnd,
   		PrecisionType prec,
   		int base){
	if(mpfr_set_str(mpfr_rep, str.c_str(), base, rnd)) {
	    std::cerr << " Problem reading from string " << std::endl;
	}
}


inline std::ostream& operator <<(std::ostream& o, const MpReal& r) {
  int base = (o.flags() & std::ios::hex) ? 16 : (o.flags() & std::ios::oct) ? 8
      : 10;
  return r.put(o, r.getDefaultRndMode(), r.getDefaultPrecision(), base,
      o.precision());
}

inline std::istream& operator >>(std::istream& i, MpReal& r) {

  if(!i)
    return i;

  // read white spaces
  i >> std::ws;

  // reading the string,
  // the conversion from a string to a mpfr is done by mpfr_set_str
  bool noend = true;
  char c;
  std::string str;

  // read the characters on i until a white space is read
  while(noend) {
    i.get(c);
    if(i.eof()) {

      if(str.size() == 0)
        return i;
      // we clear failbit from the previous operation
      i.clear(i.eofbit);
      noend = false;

    } else if((isdigit(c)) || (c =='.') || (c == 'E') || (c == 'e') || (c == '-') || (c == '+')) {
      str.push_back(c);
    } else {                  //if((isspace(c)) || (c == ',') || (c == ']')) {
      noend = false;
      i.putback(c);
    }
  }
  if(mpfr_set_str(r.mpfr_rep, str.c_str(), 10, MpReal::getDefaultRndMode())) {
    std::cerr << " Pb reading on the input stream " << std::endl;
  }
  return i;
}

}
} // end of namespace capd::multiPrec

#endif // _CAPD_MULTIPREC_MPREAL_OP_HPP_
