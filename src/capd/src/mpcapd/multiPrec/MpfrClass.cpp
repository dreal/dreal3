//

#include "capd/multiPrec/MpSetting.h"
#ifdef __HAVE_MPFR__

#include "capd/multiPrec/MpfrClass.h"
#ifdef USE_OLD_MPFRCLASS

#include <stdio.h>
#include <cstring>
/* Allocate func are defined in gmp-impl.h */

/* In newer GMP, there aren't anymore __gmp_allocate_func,
 __gmp_reallocate_func & __gmp_free_func in gmp.h
 Just getting the correct value by calling mp_get_memory_functions */

#ifdef mp_get_memory_functions

#undef __gmp_allocate_func
#undef __gmp_reallocate_func
#undef __gmp_free_func
#define MPFR_GET_MEMFUNC mp_get_memory_functions(&mpfr_allocate_func, &mpfr_reallocate_func, &mpfr_free_func)
#define __gmp_allocate_func   (MPFR_GET_MEMFUNC, mpfr_allocate_func)
#define __gmp_reallocate_func (MPFR_GET_MEMFUNC, mpfr_reallocate_func)
#define __gmp_free_func       (MPFR_GET_MEMFUNC, mpfr_free_func)
__MPFR_DECLSPEC extern void * (*mpfr_allocate_func) _MPFR_PROTO ((size_t));
__MPFR_DECLSPEC extern void * (*mpfr_reallocate_func) _MPFR_PROTO ((void *,
        size_t, size_t));
__MPFR_DECLSPEC extern void (*mpfr_free_func) _MPFR_PROTO ((void *,
        size_t));

#endif
#include "capd/auxil/logger.h"
#include <set>
namespace capd {
namespace multiPrec {

//--------------------------------------------------------------
//
// Constructors and destructors
//
//--------------------------------------------------------------
std::set<int> indexSet;

#ifdef __CAPD_MPFR_DEBUG__
int nOfMpfrObjects = 0;
int maxIndex = 0;
#define INC_INDEX(msg) index=++maxIndex; indexSet.insert(index); ++nOfMpfrObjects; capd::slog2 << "\n + (" <<index << ")("<<nOfMpfrObjects <<") : " << msg
#define DEC_INDEX(msg) --nOfMpfrObjects; indexSet.erase(index); capd::slog2 << "\n - (" <<index << ")("<<nOfMpfrObjects <<") : " << msg
#else
#define INC_INDEX(msg)
#define DEC_INDEX(msg)
#endif

MpfrClass::MpfrClass() {
  mpfr_init2(mpfr_rep, getDefaultPrecision());
  nbref = new RefCounter(0);
  inexact = new InexactFlag();
  INC_INDEX(" default ");
}

MpfrClass::MpfrClass(double d, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);

  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set_d(mpfr_rep, d, rnd);
  INC_INDEX(" double " << d);
}

MpfrClass::MpfrClass(long double d, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);

  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set_ld(mpfr_rep, d, rnd);
  INC_INDEX(" ld " << d);
}

MpfrClass::MpfrClass(int i, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set_si(mpfr_rep, (long) (i), rnd);
  INC_INDEX(" " << i);
}

MpfrClass::MpfrClass(unsigned int i, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set_ui(mpfr_rep, (unsigned long int) i, rnd);
  INC_INDEX(" " << i);

}

MpfrClass::MpfrClass(long int i, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set_si(mpfr_rep, i, rnd);
  INC_INDEX(" " << i);

}

MpfrClass::MpfrClass(unsigned long int i, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set_ui(mpfr_rep, i, rnd);
  INC_INDEX( " " << i);

}

MpfrClass::MpfrClass(std::string s, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  if(mpfr_set_str(mpfr_rep, const_cast<char *> (s.c_str()), 10, rnd)) {
    std::cerr << "Pb while reading " << s << std::endl;
    // maybe throw an exception...
  }
  INC_INDEX(" " << s);

}
MpfrClass::MpfrClass(const char * s, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  if(mpfr_set_str(mpfr_rep, s, 10, rnd)) {
    std::cerr << "Pb while reading " << s << std::endl;
    // maybe throw an exception...
  }
  INC_INDEX(" " << s);

}
MpfrClass::MpfrClass(mpz_srcptr z, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set_z(mpfr_rep, z, rnd);
  INC_INDEX(" ");

}

MpfrClass::MpfrClass(mpq_srcptr q, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set_q(mpfr_rep, q, rnd);
  INC_INDEX("");
}

MpfrClass::MpfrClass(mpfr_t r, RoundingMode rnd, PrecisionType prec) {
  mpfr_init2(mpfr_rep, prec);
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  inexact->refvalue() = mpfr_set (mpfr_rep, r, rnd);
  INC_INDEX(" ");
}

MpfrClass::MpfrClass(const MpfrClass& r) {
  mpfr_rep[0] = r.mpfr_rep[0];
  inexact = r.inexact;
  nbref = r.nbref;
  nbref->incr();
  INC_INDEX(" ");

}

MpfrClass::~MpfrClass() {
  DEC_INDEX(" destruktor " << (*this) << " ref: [" << nbref->id << "] value " << nbref->getvalue());
  if(nbref->decr() <= 0) {
    mpfr_clear(mpfr_rep);
    delete inexact;
    delete nbref;
  }
}

//--------------------------------------------------------------
//
// Assignment and physical copy
//
//--------------------------------------------------------------

// Assignment is a logical copy
MpfrClass& MpfrClass::operator =(const MpfrClass& r) {
//  capd::slog2 << "\n = (" << index << ")[ref : [" << nbref->index << "] :"
//      << nbref->getvalue() << " ] = (" << r.index << ")[ref : ["
//      << r.nbref->index << "] :" << r.nbref->getvalue() << "]";
//  //(*this).copy(r);
  if(this->nbref == r.nbref)
    return *this;
  else if(nbref->decr() <= 0) {
    mpfr_clear(mpfr_rep);
    delete nbref;
    delete inexact;
  }
  mpfr_rep[0] = r.mpfr_rep[0];
  nbref = r.nbref;
  nbref->incr();
  inexact = r.inexact;
  return *this;
}

// Physical copy
MpfrClass& MpfrClass::copy(const MpfrClass& r, RoundingMode rnd,
    PrecisionType prec) {
  if(nbref->decr() <= 0) {
    mpfr_clear(mpfr_rep);
    delete nbref;
    delete inexact;
  }
  nbref = new RefCounter(1);
  inexact = new InexactFlag();
  // If the desired precision is different from the current one
  if(prec != getDefaultPrecision()) {
    mpfr_init2(mpfr_rep, prec);
    inexact->refvalue() = mpfr_set(mpfr_rep, r.mpfr_rep, rnd);
  } else
    inexact->refvalue() = mpfr_init_set(mpfr_rep, r.mpfr_rep, rnd);

  return *this;
}

//--------------------------------------------------------------
//
// Precision and rounding: consultation, modification
//
//--------------------------------------------------------------

// ??? Rien sur les flags inexact ?
void MpfrClass::setPrecision(MpfrClass::PrecisionType newprec) {
  nbref->refvalue() = 0;
  inexact->refvalue() = UNAFFECTED_INEXACT_FLAG;
  mpfr_set_prec(mpfr_rep, newprec);
}

void MpfrClass::changePrec(RoundingMode rnd, PrecisionType prec)
// { inexact->refvalue() = mpfr_round_prec(mpfr_rep, rnd, prec); }
// above: old version for mpfr < 2.0.2
{
  if(nbref->decr() <= 0) {
    inexact->refvalue() = mpfr_prec_round(mpfr_rep, prec, rnd);
    nbref->refvalue() = 1;
  } else {
    MpfrClass tmp(*this);
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_set(mpfr_rep, tmp.mpfr_rep, rnd);
  }
}

// Rounding in the direction of rnd2 when the result is computed
// in the direction of rnd1, with a number of wrong bits given as argument.
// Should be in place or not? In place
int MpfrClass::canRound(mp_prec_t nb_wrong_bits, RoundingMode rnd1,
    RoundingMode rnd2, PrecisionType prec) {
  return mpfr_can_round(mpfr_rep, nb_wrong_bits, rnd1, rnd2, prec);
}

//--------------------------------------------------------------
//
// Constants: Pi, log(2) and Euler constant
//
//--------------------------------------------------------------

MpfrClass MpfrClass::Pi(RoundingMode rnd, PrecisionType prec) {
  MpfrClass res(0, MpfrClass::getDefaultRndMode(), prec);
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_const_pi(res.mpfr_rep, rnd);
  return res;
}

MpfrClass MpfrClass::Log2(RoundingMode rnd, PrecisionType prec) {
  MpfrClass res(0, MpfrClass::getDefaultRndMode(), prec);
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_const_log2(res.mpfr_rep, rnd);
  return res;
}

MpfrClass MpfrClass::Euler(RoundingMode rnd, PrecisionType prec) {
  MpfrClass res(0, MpfrClass::getDefaultRndMode(), prec);
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_const_euler(res.mpfr_rep, rnd);
  return res;
}

MpfrClass MpfrClass::PositiveInfinity(PrecisionType prec) {
  MpfrClass res(0, MpfrClass::getDefaultRndMode(), prec);
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = 1;
  mpfr_set_inf(res.mpfr_rep, 1);
  return res;

}

MpfrClass MpfrClass::NegativeInfinity(PrecisionType prec) {
  MpfrClass res(0, MpfrClass::getDefaultRndMode(), prec);
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = 1;
  mpfr_set_inf(res.mpfr_rep, -1);
  return res;

}

//--------------------------------------------------------------
//
// Input Output
//
//--------------------------------------------------------------

// Outputs the value on the stream o in base 'base' with 'nb_digits'
// with rounding mode rnd
std::ostream& MpfrClass::put(std::ostream& o, RoundingMode rnd,
    PrecisionType prec, int base, int nb_digits) const {
  bool neg = (sign(*this) < 0);

  if(isinf(*this)) {
    if(neg)
      o << "-";
    o << "Inf ";
    return o;
  }
  if(isnan(*this)) {
    o << "NaN";
    return o;
  }
  if(iszero(*this)) {
    if(neg)
      o << "-";
    o << "0 ";
    return o;
  }

  // Based on mpfr_get_str to create the string
  // Output done in another way (digit . fraction x E...).
  char *s, *fraction, first_digit;
  mp_exp_t e;
  int size_s;
  s = mpfr_get_str(NULL, &e, base, nb_digits, mpfr_rep, rnd);
  size_s = std::strlen(s);
  // to print the floating point
  if(s[0] == '-') {
    o << s[0];
    first_digit = s[1];
    fraction = &s[2];
    size_s++;
  } else {
    first_digit = s[0];
    fraction = &s[1];
  }
  o << first_digit << "." << fraction;
  (*__gmp_free_func)(s, size_s);
  //Recommended way: cf. below
  //free(s, size_s);
  if(--e) {
    o << "E" << e;
  }
  o << " ";
  return o;
}

std::ostream& operator <<(std::ostream& o, const MpfrClass& r) {
  int base = (o.flags() & std::ios::hex) ? 16 : (o.flags() & std::ios::oct) ? 8 : 10;
  return r.put(o, r.getDefaultRndMode(),r.getDefaultPrecision(),base,o.precision());
}

std::istream& operator >>(std::istream& i, MpfrClass& r)
// Mimicking mpfr_set_str and Integer::>> of Givaro
{
  //if (!i.good())
  // {
  // std::cerr << " Pb reading on the input stream " << std::endl;
  // maybe throw an exception...
  //}

  if(!i)
    return i;

  // read white spaces
  i >> std::ws;

  // reading the string,
  // the conversion from a string to a mpfr is done by mpfr_set_str
  bool noend = true;
  unsigned int nread = 0;
  size_t alloc_size = 100;
  char c, *str = (char *) (*__gmp_allocate_func)(alloc_size);

  // read the characters on i until a white space is read
  while(noend) {
    // read until alloc_size char are read, or a white space is encountered
    while((noend) && (nread < alloc_size)) {
      i.get(c);
      if(i.eof()) {
        noend = false;
      } else if((isspace(c)) || (c == ',') || (c == ']')) {
        noend = false;
        i.putback(c);
      } else {
        str[nread++] = c;
      }
    }

    if(nread >= alloc_size) {
      size_t old_alloc_size = alloc_size;
      alloc_size = alloc_size * 3 / 2;
      str = (char *) (*__gmp_reallocate_func)(str, old_alloc_size, alloc_size);
    }
  }
  str[nread] = '\0';
  if(r.nbref->decr() > 0) { // if mpfr_rep is used by other objects
    mpfr_init2(r.mpfr_rep, r.getPrecision()); // we create the new one
    r.nbref = new RefCounter(1);
    r.inexact = new InexactFlag();
  } else {
    r.nbref->refvalue() = 1;
  }
  if(mpfr_set_str(r.mpfr_rep, str, 10, MpfrClass::getDefaultRndMode())) {
    std::cerr << " Pb reading on the input stream " << std::endl;
    // maybe throw an exception...
  }
  (*__gmp_free_func)(str, alloc_size);
  return i;
}

//--------------------------------------------------------------
//
// Arithmetic operations
// Pb with operators: it is impossible to stick to MPFR philosophy
// which states that the result of an arithmetic op. is computed
// with the precision of the result, since the result is not yet known.
//
//--------------------------------------------------------------

// Addition-----------------------------------------------------
MpfrClass MpfrClass::operator +(const MpfrClass& b) const {

  if(iszero(*this)) {
    //b.nbref->incr();
    return b;
  } else if(iszero(b)) {
    //nbref->incr();
    return *this;
  } else // no need to check nbref counter: res has just been created
  {
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_add(res.mpfr_rep, mpfr_rep, b.mpfr_rep,
        MpfrClass::getDefaultRndMode());
    return res;
  }
}

/*
 MpfrClass operator + (const MpfrClass& a, const MpfrClass& b)
 {

 if ( iszero(b) )
 { a.nbref->incr(); return a; }
 else if ( iszero(a) )
 { b.nbref->incr(); return b; }
 else
 {
 MpfrClass res;
 res.nbref->refvalue() = 1;
 res.inexact->refvalue() = mpfr_add(res.mpfr_rep, mpfr_rep, b.mpfr_rep, MpfrClass::getDefaultRndMode());
 return res;
 }
 }
 */

MpfrClass operator +(const MpfrClass& a, const double b) {
  return a + MpfrClass(b, MpfrClass::getDefaultRndMode(), 53);
}

MpfrClass operator +(const MpfrClass& a, const int b) {
  if(b == 0) {
    return a;
  } else if(iszero(a))
    return MpfrClass(b, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  else //use the efficient mpfr_<add,sub>_ui
  { // no need to check nbref counter: res has just been created
    MpfrClass res;
    res.nbref->refvalue() = 1;
    if(b >= 0)
      res.inexact->refvalue() = mpfr_add_ui(res.mpfr_rep, a.mpfr_rep,
          (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    else
      res.inexact->refvalue() = mpfr_sub_ui(res.mpfr_rep, a.mpfr_rep,
          (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator +(const MpfrClass& a, const unsigned int b) {
  if(b == 0) {
    return a;
  } else if(iszero(a))
    return MpfrClass((unsigned long int) b, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  else // no need to check nbref counter: res has just been created
  {
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_add_ui(res.mpfr_rep, a.mpfr_rep,
        (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator +(const MpfrClass& a, const long int b) {
  if(b == 0) {
    return a;
  } else if(iszero(a))
    return MpfrClass(b, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  else //use the efficient mpfr_<add,sub>_ui
  { // no need to check nbref counter: res has just been created
    MpfrClass res;
    res.nbref->refvalue() = 1;
    if(b >= 0)
      res.inexact->refvalue() = mpfr_add_ui(res.mpfr_rep, a.mpfr_rep,
          (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    else
      res.inexact->refvalue() = mpfr_sub_ui(res.mpfr_rep, a.mpfr_rep,
          (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator +(const MpfrClass& a, const mpz_srcptr b) {
  if(mpz_cmp_si(b, 0) == 0) {
    return a;
  } else if(iszero(a))
    return MpfrClass(b, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  else // no need to check nbref counter: res has just been created
  {
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_add_z(res.mpfr_rep, a.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator +(const MpfrClass& a, const mpq_srcptr b) {
  if(mpq_cmp_ui(b, 0, 1) == 0) {
    return a;
  } else if(iszero(a))
    return MpfrClass(b, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  else // no need to check nbref counter: res has just been created
  {
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_add_q(res.mpfr_rep, a.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator +(const MpfrClass& a, const unsigned long int b) {
  if(b == 0) {
    return a;
  } else if(iszero(a))
    return MpfrClass(b, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  else // no need to check nbref counter: res has just been created
  {
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_add_ui(res.mpfr_rep, a.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass& MpfrClass::operator +=(const MpfrClass& b) {
  if(iszero(b))
    return *this;
  if(iszero(*this)) {
    if(getPrecision() == b.getPrecision()) {
      if(nbref->decr() <= 0) // no other ref. on the value of *this
      {
        mpfr_clear(mpfr_rep);
        delete nbref;
        delete inexact;
      }
      mpfr_rep[0] = b.mpfr_rep[0];
      nbref = b.nbref;
      nbref->incr();
      inexact = b.inexact;
    } else {
      if(nbref->decr() <= 0) // no other ref. on the value of *this
      { // the memory can be reused
        nbref->refvalue() = 1;
        inexact->refvalue()
            = mpfr_set(mpfr_rep, b.mpfr_rep, MpfrClass::getDefaultRndMode());
      } else // the value and memory used must be preserved
      {
        //  MpfrClass tmp (*this);
        PrecisionType prec = getPrecision();
        mpfr_init2(mpfr_rep, prec);
        nbref = new RefCounter(1);
        inexact = new InexactFlag();
        inexact->refvalue()
            = mpfr_set(mpfr_rep, b.mpfr_rep, MpfrClass::getDefaultRndMode());
      }
    }
    return *this;
  }

  // none of the operands is zero
  if(nbref->decr() <= 0) // no other ref. on the value of *this
  { // the memory can be reused
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_add(mpfr_rep, mpfr_rep, b.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  } else // the value and memory used must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_add(mpfr_rep, tmp.mpfr_rep, b.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator +=(const double b) {
  return (*this) += MpfrClass(b, MpfrClass::getDefaultRndMode(), 53);
}

MpfrClass& MpfrClass::operator +=(const long int b) // using the more efficient mpfr_add_ui
{
  if(b == 0)
    return *this;
  if(iszero(*this)) {
    *this = MpfrClass(b, MpfrClass::getDefaultRndMode(), getPrecision());
    return *this;
  }

  // none of the operands is zero
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    if(b > 0)
      inexact->refvalue() = mpfr_add_ui(mpfr_rep, mpfr_rep,
          (unsigned long int) b, MpfrClass::getDefaultRndMode());
    else
      inexact->refvalue() = mpfr_sub_ui(mpfr_rep, mpfr_rep,
          (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
  } else // the previous value and memory must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    if(b > 0)
      inexact->refvalue() = mpfr_add_ui(mpfr_rep, tmp.mpfr_rep,
          (unsigned long int) b, MpfrClass::getDefaultRndMode());
    else
      inexact->refvalue() = mpfr_sub_ui(mpfr_rep, tmp.mpfr_rep,
          (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator +=(const unsigned long int b) // using mpfr_add_ui
{
  if(b == 0)
    return *this;
  if(iszero(*this)) {
    *this = MpfrClass(b, MpfrClass::getDefaultRndMode(), getPrecision());
    return *this;
  }

  // none of the operands is zero
  if(nbref->decr() <= 0) // the memory can be reused
  {
    inexact->refvalue() = mpfr_add_ui(mpfr_rep, mpfr_rep,
        (unsigned long int) b, MpfrClass::getDefaultRndMode());
    nbref->refvalue() = 1;
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_add_ui(mpfr_rep, tmp.mpfr_rep,
        (unsigned long int) b, MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator +=(const int b) // using the efficient mpfr_add_ui
{
  return (*this) += long(b);
}

MpfrClass& MpfrClass::operator +=(const unsigned int b) // using mpfr_add_ui
{
  return (*this) += (unsigned long int) (b);
}

MpfrClass& MpfrClass::operator +=(const mpz_srcptr b) // using mpfr_add_z
{
  if(mpz_cmp_si(b, 0) == 0)
    return *this;
  if(iszero(*this)) {
    *this = MpfrClass(b, MpfrClass::getDefaultRndMode(), getPrecision());
    return *this;
  }

  // none of the operands is zero
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_add_z(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_add_z(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator +=(const mpq_srcptr b) // using mpfr_add_q
{
  if(mpq_cmp_si(b, 0, 1) == 0)
    return *this;
  if(iszero(*this)) {
    *this = MpfrClass(b, MpfrClass::getDefaultRndMode(), getPrecision());
    return *this;
  }

  // none of the operands is zero
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_add_q(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_add_q(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

void MpfrClass::add(MpfrClass& res, const MpfrClass& r1, const MpfrClass& r2,
    RoundingMode rnd)
// This function is the one where the philosophy of MPFR is preserved:
// in this function the result is computed with the precision of the result.
{
  if(iszero(r1)) {
    if(res.getPrecision() == r2.getPrecision()) {
      if(res.nbref->decr() <= 0) // the memory can be reused
      {
        mpfr_clear(res.mpfr_rep);
        delete res.nbref;
        delete res.inexact;
      }
      res.mpfr_rep[0] = r2.mpfr_rep[0];
      res.nbref = r2.nbref;
      res.nbref->incr();
      res.inexact = r2.inexact;
    } else // The result does not have the same precision as r2
    { // it must be converted and possibly rounded.
      if(res.nbref->decr() <= 0) // the memory can be reused
      {
        res.nbref->refvalue() = 1;
        res.inexact->refvalue() = mpfr_set(res.mpfr_rep, r2.mpfr_rep, rnd);
      } else // the previous memory must be preserved
      {
        PrecisionType prec = res.getPrecision();
        mpfr_init2(res.mpfr_rep, prec);
        res.nbref = new RefCounter(1);
        res.inexact = new InexactFlag(1);
        res.inexact->refvalue() = mpfr_set(res.mpfr_rep, r2.mpfr_rep, rnd);
      }
    }
  } // r1 == 0

  if(iszero(r2)) {
    if(res.getPrecision() == r1.getPrecision()) {
      if(res.nbref->decr() <= 0) // the memory can be reused
      {
        mpfr_clear(res.mpfr_rep);
        delete res.nbref;
        delete res.inexact;
      }
      res.mpfr_rep[0] = r1.mpfr_rep[0];
      res.nbref = r1.nbref;
      res.nbref->incr();
      res.inexact = r1.inexact;
    } else // The result does not have the same precision as r1
    { // it must be converted and possibly rounded.
      if(res.nbref->decr() <= 0) // the memory can be reused
      {
        res.nbref->refvalue() = 1;
        res.inexact->refvalue() = mpfr_set(res.mpfr_rep, r1.mpfr_rep, rnd);
      } else // the previous memory must be preserved
      {
        PrecisionType prec = res.getPrecision();
        mpfr_init2(res.mpfr_rep, prec);
        res.nbref = new RefCounter(1);
        res.inexact = new InexactFlag(1);
        res.inexact->refvalue() = mpfr_set(res.mpfr_rep, r1.mpfr_rep, rnd);
      }
    }
  } // r2 == 0

  // none of the operands is zero
  if(res.nbref->decr() <= 0) // the memory can be reused
  {
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_add(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  } else // the previous memory must be preserved
  {
    PrecisionType prec = res.getPrecision();
    mpfr_init2(res.mpfr_rep, prec);
    res.nbref = new RefCounter(1);
    res.inexact = new InexactFlag(1);
    res.inexact->refvalue() = mpfr_add(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  }
}

// Subtraction --------------------------------------------------------
MpfrClass MpfrClass::operator -(const MpfrClass& b) const {
  MpfrClass res;
  res.nbref->refvalue() = 1;
  //if(iszero(*this))
  //  std::cout << " ==0==";
  res.inexact->refvalue() = mpfr_sub(res.mpfr_rep, mpfr_rep, b.mpfr_rep,
      MpfrClass::getDefaultRndMode());
//  std::cout << "inexact(-) " << res.inexact->getvalue();
  return res;
}

MpfrClass operator -(const MpfrClass& a, const double b) {
  return a - MpfrClass(b, MpfrClass::getDefaultRndMode(), 53);
}

MpfrClass operator -(const MpfrClass &a, const int b) {
  if(b == 0) {
    return a;
  } else if(iszero(a))
    return MpfrClass((-b), MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  else //use the efficient mpfr_<add,sub>_ui
  { // no need to check nbref counter: res has just been created
    MpfrClass res;
    res.nbref->refvalue() = 1;
    if(b >= 0)
      res.inexact->refvalue() = mpfr_sub_ui(res.mpfr_rep, a.mpfr_rep,
          (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    else
      res.inexact->refvalue() = mpfr_add_ui(res.mpfr_rep, a.mpfr_rep,
          (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator -(const MpfrClass &a, const unsigned int b) {
  if(b == 0) {
    return a;
  } else if(iszero(a)) {
    int tmp;
    tmp = b;
    return MpfrClass((-tmp), MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  } else //use the efficient mpfr_<add,sub>_ui
  { // no need to check nbref counter: res has just been created
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_sub_ui(res.mpfr_rep, a.mpfr_rep,
        (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator -(const MpfrClass &a, const long int b) {
  if(b == 0) {
    return a;
  } else if(iszero(a))
    return MpfrClass((-b), MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  else //use the efficient mpfr_<add,sub>_ui
  { // no need to check nbref counter: res has just been created
    MpfrClass res;
    res.nbref->refvalue() = 1;
    if(b >= 0)
      res.inexact->refvalue() = mpfr_sub_ui(res.mpfr_rep, a.mpfr_rep,
          (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    else
      res.inexact->refvalue() = mpfr_add_ui(res.mpfr_rep, a.mpfr_rep,
          (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator -(const MpfrClass &a, const unsigned long int b) {
  if(b == 0) {
    return a;
  } else if(iszero(a)) {
    long int tmp;
    tmp = b;
    return MpfrClass((-tmp), MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  } else //use the efficient mpfr_<add,sub>_ui
  { // no need to check nbref counter: res has just been created
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_sub_ui(res.mpfr_rep, a.mpfr_rep,
        (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator -(const MpfrClass& a, const mpz_srcptr b) {
  if(mpz_cmp_si(b, 0) == 0) {
    return a;
  } else if(iszero(a))
    return (-MpfrClass(b, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision()));
  else // no need to check nbref counter: res has just been created
  {
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_sub_z(res.mpfr_rep, a.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator -(const MpfrClass& a, const mpq_srcptr b) {
  if(mpq_cmp_ui(b, 0, 1) == 0) {
    return a;
  } else if(iszero(a))
    return (-MpfrClass(b, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision()));
  else // no need to check nbref counter: res has just been created
  {
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_sub_q(res.mpfr_rep, a.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator -(const double a, const MpfrClass& b) {
  return MpfrClass(a, MpfrClass::getDefaultRndMode(), 53) - b;
}

MpfrClass operator -(const int a, const MpfrClass& b) {
  return (MpfrClass(a, MpfrClass::getDefaultRndMode(), sizeof(int)) - b);
}

MpfrClass operator -(const unsigned int a, const MpfrClass& b) {
  if(a == 0)
    return (-b);
  else if(iszero(b)) {
    return MpfrClass((unsigned long int) (a), MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  } else //use the efficient mpfr_ui_sub
  { // no need to check nbref counter: res has just been created
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_ui_sub(res.mpfr_rep,
        (unsigned long int) (a), b.mpfr_rep, MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator -(const long int a, const MpfrClass& b) {
  return (MpfrClass(a, MpfrClass::getDefaultRndMode(), sizeof(long int)) - b);
}

MpfrClass operator -(const unsigned long int a, const MpfrClass& b) {
  if(a == 0)
    return (-b);
  else if(iszero(b)) {
    return MpfrClass(a, MpfrClass::getDefaultRndMode(),
        MpfrClass::getDefaultPrecision());
  } else //use the efficient mpfr_<add,sub>_ui
  { // no need to check nbref counter: res has just been created
    MpfrClass res;
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_ui_sub(res.mpfr_rep, a, b.mpfr_rep,
        MpfrClass::getDefaultRndMode());
    return res;
  }
}

MpfrClass operator -(const mpz_srcptr a, const MpfrClass& b) {
  return (MpfrClass(a, MpfrClass::getDefaultRndMode(), sizeof(int)) - b);
}

MpfrClass operator -(const mpq_srcptr a, const MpfrClass& b) {
  return (MpfrClass(a, MpfrClass::getDefaultRndMode(), sizeof(int)) - b);
}

MpfrClass MpfrClass::operator -() const {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_neg(res.mpfr_rep, mpfr_rep,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass& MpfrClass::operator -=(const MpfrClass& b) {
  if(iszero(b))
    return *this;
  if(this == &b){
    mpfr_set_ui(mpfr_rep,0,MpfrClass::getDefaultRndMode());
    /////////////////////////
    //    TODO
  }
  else
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    if(iszero(*this))
      inexact->refvalue() = mpfr_neg(mpfr_rep, b.mpfr_rep,
          MpfrClass::getDefaultRndMode());
    else
      inexact->refvalue() = mpfr_sub(mpfr_rep, mpfr_rep, b.mpfr_rep,
          MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    if(iszero(tmp)){
      inexact->refvalue() = mpfr_neg(mpfr_rep, b.mpfr_rep,
          MpfrClass::getDefaultRndMode());
      std::cout << " =0= inexact : " << inexact->val();
    }else
      inexact->refvalue() = mpfr_sub(mpfr_rep, tmp.mpfr_rep, b.mpfr_rep,
          MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator -=(const double b) {
  return (*this) -= MpfrClass(b, MpfrClass::getDefaultRndMode(), 53);
}

MpfrClass& MpfrClass::operator -=(const int b) {
  (*this) += -b;
  return *this;
}

MpfrClass& MpfrClass::operator -=(const long int b) {
  (*this) += -b;
  return *this;
}

MpfrClass& MpfrClass::operator -=(const unsigned long int b) // using the more efficient mpfr_sub_ui
{
  if(b == 0)
    return *this;
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_sub_ui(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_sub_ui(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator -=(const unsigned int b) {
  (*this) -= (unsigned long int) b;
  return *this;
}

MpfrClass& MpfrClass::operator -=(const mpz_srcptr b) // using mpfr_sub_z
{
  if(mpz_cmp_si(b, 0) == 0)
    return *this;
  if(iszero(*this)) {
    *this = -MpfrClass(b, MpfrClass::getDefaultRndMode(), getPrecision());
    return *this;
  }

  // none of the operands is zero
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_sub_z(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_sub_z(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator -=(const mpq_srcptr b) // using mpfr_sub_q
{
  if(mpq_cmp_si(b, 0, 1) == 0)
    return *this;
  if(iszero(*this)) {
    *this = -MpfrClass(b, MpfrClass::getDefaultRndMode(), getPrecision());
    return *this;
  }

  // none of the operands is zero
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_sub_q(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_sub_q(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

void MpfrClass::neg(MpfrClass& res, const MpfrClass& r, RoundingMode rnd) {
  if(res.nbref->decr() <= 0) // the memory can be reused
  {
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_neg(res.mpfr_rep, r.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    PrecisionType prec = res.getPrecision();
    mpfr_init2(res.mpfr_rep, prec);
    res.nbref = new RefCounter(1);
    res.inexact = new InexactFlag();
    res.inexact->refvalue() = mpfr_neg(res.mpfr_rep, r.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  }
}

void MpfrClass::sub(MpfrClass& res, const MpfrClass& r1, const MpfrClass& r2,
    RoundingMode rnd) {
  if(res.nbref->decr() <= 0) {
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_sub(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    PrecisionType prec = res.getPrecision();
    mpfr_init2(res.mpfr_rep, prec);
    res.nbref = new RefCounter(1);
    res.inexact = new InexactFlag();
    res.inexact->refvalue() = mpfr_sub(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  }
}

// Multiplication-----------------------------------------------
MpfrClass MpfrClass::operator *(const MpfrClass& b) const {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_mul(res.mpfr_rep, mpfr_rep, b.mpfr_rep,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator *(const MpfrClass& a, const double b) {
  return a * MpfrClass(b, MpfrClass::getDefaultRndMode(), 53);
}

MpfrClass operator *(const MpfrClass& a, const int b) {
  return a * MpfrClass(b, MpfrClass::getDefaultRndMode(), sizeof(int));
}

MpfrClass operator *(const MpfrClass& a, const unsigned int b) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_mul_ui(res.mpfr_rep, a.mpfr_rep,
      (unsigned long int) (b), MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator *(const MpfrClass& a, const long int b) {
  return a * MpfrClass(b, MpfrClass::getDefaultRndMode(), sizeof(long int));
}

MpfrClass operator *(const MpfrClass& a, const unsigned long int b) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_mul_ui(res.mpfr_rep, a.mpfr_rep, b,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator *(const MpfrClass& a, const mpz_srcptr b) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_mul_z(res.mpfr_rep, a.mpfr_rep, b,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator *(const MpfrClass& a, const mpq_srcptr b) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_mul_q(res.mpfr_rep, a.mpfr_rep, b,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator *(const double a, const MpfrClass& b) {
  return MpfrClass(a, MpfrClass::getDefaultRndMode(), 53) * b;
}

MpfrClass operator *(const int a, const MpfrClass& b) {
  return MpfrClass(a, MpfrClass::getDefaultRndMode(), sizeof(int)) * b;
}

MpfrClass operator *(const unsigned int a, const MpfrClass& b) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_mul_ui(res.mpfr_rep, b.mpfr_rep,
      (unsigned long int) (a), MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator *(const long int a, const MpfrClass& b) {
  return MpfrClass(a, MpfrClass::getDefaultRndMode(), sizeof(long int)) * b;
}

MpfrClass operator *(const mpz_srcptr a, const MpfrClass& b) {
  return b * a;
}

MpfrClass operator *(const mpq_srcptr a, const MpfrClass& b) {
  return b * a;
}

MpfrClass operator *(const unsigned long int a, const MpfrClass& b) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_mul_ui(res.mpfr_rep, b.mpfr_rep, a,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass& MpfrClass::operator *=(const MpfrClass& b) {
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_mul(mpfr_rep, mpfr_rep, b.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_mul(mpfr_rep, tmp.mpfr_rep, b.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator *=(const double b) {
  return (*this) *= MpfrClass(b, MpfrClass::getDefaultRndMode(), 53);
}

MpfrClass& MpfrClass::operator *=(const long int b) // using the more efficient mpfr_mul_ui
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    if(b >= 0)
      inexact->refvalue() = mpfr_mul_ui(mpfr_rep, mpfr_rep,
          (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    else {
      int dummy;
      inexact->refvalue() = mpfr_mul_ui(mpfr_rep, mpfr_rep,
          (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
      dummy = mpfr_neg(mpfr_rep, mpfr_rep, MpfrClass::getDefaultRndMode());
      inexact->refvalue() = -inexact->getvalue();
    }
  } else // the previous value must be preserved
  {
    MpfrClass tmp(*this);
    int dummy;
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    if(b >= 0)
      inexact->refvalue() = mpfr_mul_ui(mpfr_rep, tmp.mpfr_rep,
          (unsigned long int) (b), MpfrClass::getDefaultRndMode());
    else {
      inexact->refvalue() = mpfr_mul_ui(mpfr_rep, tmp.mpfr_rep,
          (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
      dummy = mpfr_neg(mpfr_rep, mpfr_rep, MpfrClass::getDefaultRndMode());
      inexact->refvalue() = -inexact->getvalue();
    }
  }
  return *this;
}

MpfrClass& MpfrClass::operator *=(const int b) {
  (*this) *= (long int) (b);
  return *this;
}

MpfrClass& MpfrClass::operator *=(const unsigned long int b) // the efficient mpfr_mul_ui is used
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_mul_ui(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_mul_ui(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator *=(const unsigned int b) {
  (*this) *= (unsigned long int) (b);
  return *this;
}

MpfrClass& MpfrClass::operator *=(const mpz_srcptr b) // using mpfr_mul_z
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_mul_z(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_mul_z(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator *=(const mpq_srcptr b) // using mpfr_mul_q
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_mul_q(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_mul_q(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

void MpfrClass::mul(MpfrClass& res, const MpfrClass& r1, const MpfrClass& r2,
    RoundingMode rnd) {
  if(res.nbref->decr() <= 0) // the memory can be reused
  {
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_mul(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    PrecisionType prec = res.getPrecision();
    mpfr_init2(res.mpfr_rep, prec);
    res.nbref = new RefCounter(1);
    res.inexact = new InexactFlag();
    res.inexact->refvalue() = mpfr_mul(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  }
}

// Division-----------------------------------------------------
MpfrClass MpfrClass::operator /(const MpfrClass& b) const {

  MpfrClass res;
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_div(res.mpfr_rep, mpfr_rep, b.mpfr_rep,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator /(const MpfrClass& a, const double b) {
  return a / MpfrClass(b, MpfrClass::getDefaultRndMode(), 53);
}

MpfrClass operator /(const MpfrClass& a, const int b) {
  return a / MpfrClass(b, MpfrClass::getDefaultRndMode(), sizeof(int));
}

MpfrClass operator /(const MpfrClass& a, const unsigned int b) {
  MpfrClass res;
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_div_ui(res.mpfr_rep, a.mpfr_rep,
      (unsigned long int) (b), MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator /(const MpfrClass& a, const long int b) {
  return a / MpfrClass(b, MpfrClass::getDefaultRndMode(), sizeof(long int));
}

MpfrClass operator /(const MpfrClass& a, const unsigned long int b) {
  MpfrClass res;
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_div_ui(res.mpfr_rep, a.mpfr_rep, b,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator /(const MpfrClass& a, const mpz_srcptr b) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_div_z(res.mpfr_rep, a.mpfr_rep, b,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator /(const MpfrClass& a, const mpq_srcptr b) {
  MpfrClass res;

  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_div_q(res.mpfr_rep, a.mpfr_rep, b,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator /(const double a, const MpfrClass& b) {
  return MpfrClass(a, MpfrClass::getDefaultRndMode(), 53) / b;
}

MpfrClass operator /(const long int a, const MpfrClass& b) {
  return MpfrClass(a, MpfrClass::getDefaultRndMode(), sizeof(long int)) / b;
}

MpfrClass operator /(const int a, const MpfrClass& b) {
  return (long) a / b;
}

MpfrClass operator /(const unsigned long int a, const MpfrClass& b) // using mpfr_ui_div
{
  MpfrClass res;
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_ui_div(res.mpfr_rep, a, b.mpfr_rep,
      MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator /(const unsigned int a, const MpfrClass& b) {
  MpfrClass res;
  res.nbref->refvalue() = 1;
  res.inexact->refvalue() = mpfr_ui_div(res.mpfr_rep, (unsigned long int) (a),
      b.mpfr_rep, MpfrClass::getDefaultRndMode());
  return res;
}

MpfrClass operator /(const mpz_srcptr a, const MpfrClass& b) {
  return MpfrClass(a) / b;
}

MpfrClass operator /(const mpq_srcptr a, const MpfrClass& b) {
  return MpfrClass(a) / b;
}

MpfrClass& MpfrClass::operator /=(const MpfrClass& b) {
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_div(mpfr_rep, mpfr_rep, b.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    mpfr_div(mpfr_rep, tmp.mpfr_rep, b.mpfr_rep, MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator /=(const double b) {
  return (*this)
      /= MpfrClass(b, MpfrClass::getDefaultRndMode(), getPrecision());
}

MpfrClass& MpfrClass::operator /=(const long int b) // using the more efficient mpfr_div_ui
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    if(b > 0)
      inexact->refvalue() = mpfr_div_ui(mpfr_rep, mpfr_rep,
          (unsigned long int) b, MpfrClass::getDefaultRndMode());
    else {
      if(MpfrClass::getDefaultRndMode() == RoundDown)
        inexact->refvalue() = mpfr_div_ui(mpfr_rep, mpfr_rep,
            (unsigned long int) (-b), RoundUp);
      else if(MpfrClass::getDefaultRndMode() == RoundUp)
        inexact->refvalue() = mpfr_div_ui(mpfr_rep, mpfr_rep,
            (unsigned long int) (-b), RoundDown);
      else
        inexact->refvalue() = mpfr_div_ui(mpfr_rep, mpfr_rep,
            (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
      //int dummy =
      mpfr_neg(mpfr_rep, mpfr_rep, MpfrClass::getDefaultRndMode());
      inexact->refvalue() = -inexact->getvalue();
    }
  } else // the previous value must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    if(b > 0)
      inexact->refvalue() = mpfr_div_ui(mpfr_rep, tmp.mpfr_rep,
          (unsigned long int) b, MpfrClass::getDefaultRndMode());
    else {
      if(MpfrClass::getDefaultRndMode() == RoundDown)
        inexact->refvalue() = mpfr_div_ui(mpfr_rep, mpfr_rep,
            (unsigned long int) (-b), RoundUp);
      else if(MpfrClass::getDefaultRndMode() == RoundUp)
        inexact->refvalue() = mpfr_div_ui(mpfr_rep, mpfr_rep,
            (unsigned long int) (-b), RoundDown);
      else
        inexact->refvalue() = mpfr_div_ui(mpfr_rep, mpfr_rep,
            (unsigned long int) (-b), MpfrClass::getDefaultRndMode());
      //int dummy =
      mpfr_neg(mpfr_rep, mpfr_rep, MpfrClass::getDefaultRndMode());
      inexact->refvalue() = -inexact->getvalue();
    }
  }
  return *this;
}

MpfrClass& MpfrClass::operator /=(const int b) {
  (*this) /= (long int) b;
  return *this;
}

MpfrClass& MpfrClass::operator /=(const unsigned long int b) // using mpfr_div_ui
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_div_ui(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact->refvalue() = mpfr_div_ui(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator /=(const unsigned int b) {
  (*this) /= (unsigned long int) b;
  return *this;
}

MpfrClass& MpfrClass::operator /=(const mpz_srcptr b) // using mpfr_div_z
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_div_z(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_div_z(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

MpfrClass& MpfrClass::operator /=(const mpq_srcptr b) // using mpfr_div_q
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    inexact->refvalue() = mpfr_div_q(mpfr_rep, mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  } else {
    MpfrClass tmp(*this);
    PrecisionType prec = getPrecision();
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
    inexact->refvalue() = mpfr_div_q(mpfr_rep, tmp.mpfr_rep, b,
        MpfrClass::getDefaultRndMode());
  }
  return *this;
}

void MpfrClass::div(MpfrClass& res, const MpfrClass& r1, const MpfrClass& r2,
    RoundingMode rnd) {
  if(res.nbref->decr() <= 0) // the memory can be reused
  {
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_div(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    PrecisionType prec = res.getPrecision();
    mpfr_init2(res.mpfr_rep, prec);
    res.nbref = new RefCounter(1);
    res.inexact = new InexactFlag();
    res.inexact->refvalue() = mpfr_div(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        MpfrClass::getDefaultRndMode());
  }
}

void MpfrClass::fma(MpfrClass& res, const MpfrClass& r1, const MpfrClass& r2,
    const MpfrClass& r3, RoundingMode rnd) {
  if(res.nbref->decr() <= 0) // the memory can be reused
  {
    res.nbref->refvalue() = 1;
    res.inexact->refvalue() = mpfr_fma(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        r3.mpfr_rep, MpfrClass::getDefaultRndMode());
  } else // the previous value must be preserved
  {
    PrecisionType prec = res.getPrecision();
    mpfr_init2(res.mpfr_rep, prec);
    res.nbref = new RefCounter(1);
    res.inexact = new InexactFlag();
    res.inexact->refvalue() = mpfr_fma(res.mpfr_rep, r1.mpfr_rep, r2.mpfr_rep,
        r3.mpfr_rep, MpfrClass::getDefaultRndMode());
  }
}

//--------------------------------------------------------------
//
// Mathematical and miscellaneous functions
//
//--------------------------------------------------------------
// NaN of infinity handled by MPFR
// => no test on the value (sign...) of the operand
void MpfrClass::random(PrecisionType prec) // member to avoid conflict with GMP random
{
  if(nbref->decr() <= 0) // the memory can be reused
  {
    nbref->refvalue() = 1;
    mpfr_set_prec(mpfr_rep, prec);
  } else // the previous value must be preserved
  {
    mpfr_init2(mpfr_rep, prec);
    nbref = new RefCounter(1);
    inexact = new InexactFlag();
  }
  mpfr_random(mpfr_rep);
  inexact->refvalue() = EXACT_FLAG;
}

void sin_cos(MpfrClass& res_sin, MpfrClass& res_cos, const MpfrClass& r,
    RoundingMode rnd) {
  int inexact;

  if(res_sin.nbref->decr() <= 0) {
    res_sin.nbref->refvalue() = 1;
  } else {
    MpfrClass::PrecisionType prec = res_sin.getPrecision();
    mpfr_init2(res_sin.mpfr_rep, prec);
    res_sin.nbref = new RefCounter(1);
  }
  if(res_cos.nbref->decr() <= 0) {
    res_cos.nbref->refvalue() = 1;
  } else {
    MpfrClass::PrecisionType prec = res_cos.getPrecision();
    mpfr_init2(res_cos.mpfr_rep, prec);
    res_cos.nbref = new RefCounter(1);
  }
  inexact = mpfr_sin_cos(res_sin.mpfr_rep, res_cos.mpfr_rep, r.mpfr_rep, rnd);
  if(inexact == 0) {
    res_sin.inexact->refvalue() = EXACT_FLAG;
    res_cos.inexact->refvalue() = EXACT_FLAG;
  } else {
    res_sin.inexact->refvalue() = UNAFFECTED_INEXACT_FLAG;
    res_cos.inexact->refvalue() = UNAFFECTED_INEXACT_FLAG;
  }
}

}
} // end of namespace capd::multiPrec
#endif  // USE_OLD_MPFRCLASS
#endif  // __HAVE_MPFR__
