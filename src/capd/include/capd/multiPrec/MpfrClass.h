/*
 *  WARNING:  Deprecated header.   Use MpReal.h instead!
 *
 *  MpfrClass has many bugs!
 */


// uncomment the following line if you want to use old buggy MpfrClass instead of MpReal class
// left mainly for backward compatibility
// #define USE_OLD_MPFRCLASS



#ifdef __HAVE_MPFR__

#ifndef _CAPD_MULTIPREC_MPFRCLASS_H_
#define _CAPD_MULTIPREC_MPFRCLASS_H_

#ifndef USE_OLD_MPFRCLASS
#include "capd/multiPrec/MpReal.h"

namespace capd{
namespace multiPrec{

// for backward compatibility we define MpfrClass
typedef MpReal MpfrClass;

}}

#else

// C++ Interface for MPFR
// autor: Natalie Revol
// NR 21-11-00 (first steps in C++...)
// NR 23-02-04 (next steps in C++...)

#include "capd/multiPrec/MpSetting.h"


#include <cstdio>
#include <iostream>
#include <cmath>
#include <cstddef>

//#define __CAPD_MPFR_DEBUG__
#ifdef __CAPD_MPFR_DEBUG__
#include "capd/auxil/Counter.h"
#endif

//extern "C" {
#include <gmp.h>
#include <mpfr.h>
//}

namespace capd{
namespace multiPrec{
   
#ifndef _GIVARO_REF_COUNTER_H_
#define _GIVARO_REF_COUNTER_H_
// ==================================================================== //
// Definition of the Counter class, Counter
// (c) copyright GIVARO 1994                                            
// author: Th. Gautier                                                
// version : 2.7
// date: 1995
// This class definition objects to handle reference
// counter for memory allocation (eg array0). 
// ====================================================================

#ifdef __CAPD_MPFR_DEBUG__
class RefCounter : public capd::auxil::Counter<RefCounter> {
#else
class RefCounter {
#endif
public:
   // Cstor and Dstor
inline RefCounter( long l = 0) : counter(l) {} 
//inline RefCounter( const RefCounter& ) : counter(C.counter) {} 
inline ~RefCounter() {}

  //  Return the value
inline long  getvalue() const { return counter ; } 
inline long  val() const { return counter ; }
  // Return a ref to the counter
inline long& refvalue() {
   return counter ; }
  // Increments the counter and returns the new value 
inline long  incr() {
  return ++counter ;
}
  // Decrements the value and returns the new value 
inline long  decr() {
  return --counter ;
}

protected:
  long counter ;
} ;

#endif
// ==================================================================== //
// End of definition of the Counter class, Counter
// ==================================================================== //

#undef isinf
#undef isnan

#define UNAFFECTED_INEXACT_FLAG 500
#define EXACT_FLAG 0
#define INEXACT_FLAG 25
class InexactFlag {
public:
   // Cstor and Dstor
  inline InexactFlag( int l = UNAFFECTED_INEXACT_FLAG) : inexact_flag(l) {} 
  inline ~InexactFlag() {}

  //  Return the value
  inline int  getvalue() const { return inexact_flag ; } 
  inline int  val() const { return inexact_flag ; }
  // Return a ref to the inexact_flag
  inline int& refvalue() { return inexact_flag ; }

protected:
  int inexact_flag ;
} ;



// Rounding modes
typedef mp_rnd_t RoundingMode;
static const RoundingMode RoundUp=mp_rnd_t(GMP_RNDU); 
static const RoundingMode RoundDown=mp_rnd_t(GMP_RNDD); 
static const RoundingMode RoundNearest=mp_rnd_t(GMP_RNDN); 
static const RoundingMode RoundToZero=mp_rnd_t(GMP_RNDZ);

typedef mp_prec_t PrecisionType;

class MpfrClass {

  protected:
    mpfr_t mpfr_rep;	// representation of the real in a mpfr format
    // Precision
    InexactFlag *inexact;
   
    RefCounter *nbref;
    
    int index;

    // no more direct access to this variables in mpfr 
    //static PrecisionType &CurrPrecision;
    // Current default rounding mode
    //static RoundingMode &CurrRndMode;

  public:
    // constructors and destructors
    // Rounding modes
    typedef mp_rnd_t RoundingMode;
    static const RoundingMode RoundUp=mp_rnd_t(GMP_RNDU);
    static const RoundingMode RoundDown=mp_rnd_t(GMP_RNDD);
    static const RoundingMode RoundNearest=mp_rnd_t(GMP_RNDN);
    static const RoundingMode RoundToZero=mp_rnd_t(GMP_RNDZ);

    typedef mp_prec_t PrecisionType;

    MpfrClass ();
    MpfrClass (double d,
              RoundingMode rnd =  getDefaultRndMode(),
              PrecisionType prec = getDefaultPrecision());
    MpfrClass (long double d,
              RoundingMode rnd = getDefaultRndMode(),
              PrecisionType prec = getDefaultPrecision());
    MpfrClass (int i, 
              RoundingMode rnd = getDefaultRndMode(), 
              PrecisionType prec = getDefaultPrecision());
    MpfrClass (unsigned int i, 
              RoundingMode rnd = getDefaultRndMode(), 
              PrecisionType prec = getDefaultPrecision());
    MpfrClass (long int i, 
              RoundingMode rnd = getDefaultRndMode(), 
              PrecisionType prec = getDefaultPrecision());
   MpfrClass (unsigned long int i, 
              RoundingMode rnd = getDefaultRndMode(), 
              PrecisionType prec = getDefaultPrecision());
    MpfrClass(std::string s,
              RoundingMode rnd = getDefaultRndMode(),
              PrecisionType prec = getDefaultPrecision());
    MpfrClass(const char * str,
              RoundingMode rnd = getDefaultRndMode(),
              PrecisionType prec = getDefaultPrecision());
    MpfrClass (mpz_srcptr z,
              RoundingMode rnd = getDefaultRndMode(),
              PrecisionType prec = getDefaultPrecision());
    MpfrClass (mpq_srcptr q, 
              RoundingMode rnd = getDefaultRndMode(),
              PrecisionType prec = getDefaultPrecision());
    MpfrClass (mpfr_t r,
              RoundingMode rnd = getDefaultRndMode(),
              PrecisionType prec = getDefaultPrecision());
    MpfrClass (const MpfrClass& r);

    ~MpfrClass ();
 
    // Assignment and copy operators
    MpfrClass& operator = (const MpfrClass& r);
    MpfrClass& copy (const MpfrClass& r, 
                    RoundingMode rnd = getDefaultRndMode(), 
                    PrecisionType prec = getDefaultPrecision());

    // Is equal to zero?
    friend bool iszero(const MpfrClass& r) { return (mpfr_zero_p(r.mpfr_rep) != 0); }
    friend bool isinf(const MpfrClass& r) { return (mpfr_inf_p(r.mpfr_rep) != 0); }
    friend bool isnan(const MpfrClass& r) { return (mpfr_nan_p(r.mpfr_rep) != 0); }
    friend bool isnumber(const MpfrClass& r) { return (mpfr_number_p(r.mpfr_rep) != 0); }
    friend bool isSingular(const MpfrClass & r) {return (mpfr_zero_p(r.mpfr_rep) != 0); } 
    friend int sign(const MpfrClass& r) { return (mpfr_sgn(r.mpfr_rep)); }

    // Precision and rounding mode
    static void setDefaultPrecision (PrecisionType newprec);
    void setPrecision (PrecisionType newprec);
    static const PrecisionType getDefaultPrecision ();
    PrecisionType getPrecision () const;
    static void setDefaultRndMode (RoundingMode newrndmode);
    static const RoundingMode getDefaultRndMode();
    static void roundUp();
    static void roundDown();
    static void roundNearest();
    static void roundCut();

    // Changing the precision: should be in place or not? In place
    // => to round not in place, copy and round
    void changePrec (RoundingMode rnd = getDefaultRndMode(),
                     PrecisionType prec = getDefaultPrecision());

    // Rounding in the direction of rnd2 when the result is computed 
    // in the direction of rnd1, with a number of wrong bits given as argument.
    // Should be in place or not? In place
    int canRound (mp_prec_t nb_wrong_bits, RoundingMode rnd1 = getDefaultRndMode(),
                  RoundingMode rnd2 = getDefaultRndMode(),
                  PrecisionType prec = getDefaultPrecision());

    // "Constants" (but they depend on the precision and the rounding mode)
    static MpfrClass Pi(RoundingMode rnd = getDefaultRndMode(), 
                        PrecisionType prec = getDefaultPrecision()) ;
    static MpfrClass Log2(RoundingMode rnd = getDefaultRndMode(), 
                        PrecisionType prec = getDefaultPrecision()) ;
    static MpfrClass Euler(RoundingMode rnd = getDefaultRndMode(), 
                        PrecisionType prec = getDefaultPrecision()) ;
    static MpfrClass PositiveInfinity(PrecisionType prec = getDefaultPrecision());
    static MpfrClass NegativeInfinity(PrecisionType prec = getDefaultPrecision());
    

    // Comparison operators
    friend int compare (const MpfrClass& r1, const MpfrClass& r2);
    friend int compare (const MpfrClass& r1, const double r2);
    friend int compare (const MpfrClass& r1, const int r2);
    friend int compare (const MpfrClass& r1, const unsigned int r2);
    friend int compare (const MpfrClass& r1, const long int r2);
    friend int compare (const MpfrClass& r1, const unsigned long int r2);


    // Arithmetic operators
    // Philosophy: are members only the operations between MpfrClass 
    //static MpfrClass& operator+ (const MpfrClass& r1, const MpfrClass& r2) ;
    MpfrClass operator+ (const MpfrClass& r) const;
    friend MpfrClass operator+ (const MpfrClass& r1, const double r2) ;
    friend MpfrClass operator+ (const MpfrClass& r1, const int r2) ;
    friend MpfrClass operator+ (const MpfrClass& r1, const unsigned int r2) ;
    friend MpfrClass operator+ (const MpfrClass& r1, const long int r2) ;
    friend MpfrClass operator+ (const MpfrClass& r1, const unsigned long int r2) ;
    friend MpfrClass operator+ (const MpfrClass& r1, const mpz_srcptr r2) ;
    friend MpfrClass operator+ (const MpfrClass& r1, const mpq_srcptr r2) ;
    friend MpfrClass operator+ (const double r1, const MpfrClass& r2) ;
    friend MpfrClass operator+ (const int r1, const MpfrClass& r2) ;
    friend MpfrClass operator+ (const unsigned int r1, const MpfrClass& r2) ;
    friend MpfrClass operator+ (const long int r1, const MpfrClass& r2) ;
    friend MpfrClass operator+ (const unsigned long int r1, const MpfrClass& r2) ;
    friend MpfrClass operator+ (const mpz_srcptr r1, const MpfrClass& r2) ;
    friend MpfrClass operator+ (const mpq_srcptr r1, const MpfrClass& r2) ;
    MpfrClass& operator+= (const MpfrClass& r) ;
    MpfrClass& operator+= (const double r) ;
    MpfrClass& operator+= (const int r) ;
    MpfrClass& operator+= (const unsigned int r) ;
    MpfrClass& operator+= (const long int r) ;
    MpfrClass& operator+= (const unsigned long int r) ;
    MpfrClass& operator+= (const mpz_srcptr r) ;
    MpfrClass& operator+= (const mpq_srcptr r) ;
    static void add (MpfrClass& res, 
                          const MpfrClass& r1, const MpfrClass& r2,
                          RoundingMode rnd = getDefaultRndMode());

    //static MpfrClass& operator- (const MpfrClass& r1, const MpfrClass& r2);
    MpfrClass operator- (const MpfrClass& r) const;
    friend MpfrClass operator- (const MpfrClass& r1, const double r2) ;
    friend MpfrClass operator- (const MpfrClass& r1, const int r2);
    friend MpfrClass operator- (const MpfrClass& r1, const unsigned int r2);
    friend MpfrClass operator- (const MpfrClass& r1, const long int r2);
    friend MpfrClass operator- (const MpfrClass& r1, const unsigned long int r2);
    friend MpfrClass operator- (const MpfrClass& r1, const mpz_srcptr r2);
    friend MpfrClass operator- (const MpfrClass& r1, const mpq_srcptr r2);
    friend MpfrClass operator- (const double r1, const MpfrClass& r2);
    friend MpfrClass operator- (const int r1, const MpfrClass& r2);
    friend MpfrClass operator- (const unsigned int r1, const MpfrClass& r2);
    friend MpfrClass operator- (const long int r1, const MpfrClass& r2);
    friend MpfrClass operator- (const unsigned long int r1, const MpfrClass& r2);
    friend MpfrClass operator- (const mpz_srcptr r1, const MpfrClass& r2);
    friend MpfrClass operator- (const mpq_srcptr r1, const MpfrClass& r2);
    MpfrClass operator- () const;
    MpfrClass& operator-= (const MpfrClass& r) ;
    MpfrClass& operator-= (const double r) ;
    MpfrClass& operator-= (const int r) ;
    MpfrClass& operator-= (const long int r) ;
    MpfrClass& operator-= (const unsigned int r) ;
    MpfrClass& operator-= (const unsigned long int r) ;
    MpfrClass& operator-= (const mpz_srcptr r) ;
    MpfrClass& operator-= (const mpq_srcptr r) ;
    static void neg (MpfrClass& res, 
                          const MpfrClass& r, 
                          RoundingMode rnd = getDefaultRndMode());
    static void sub (MpfrClass& res, 
                          const MpfrClass& r1, const MpfrClass& r2,
                          RoundingMode rnd = getDefaultRndMode());

    //static MpfrClass& operator* (const MpfrClass& r1, const MpfrClass& r2) ;
    MpfrClass operator* (const MpfrClass& r) const;
    friend MpfrClass operator* (const MpfrClass& r1, const double r2) ;
    friend MpfrClass operator* (const MpfrClass& r1, const int r2) ;
    friend MpfrClass operator* (const MpfrClass& r1, const unsigned int r2) ;
    friend MpfrClass operator* (const MpfrClass& r1, const long int r2) ;
    friend MpfrClass operator* (const MpfrClass& r1, const unsigned long int r2) ;
    friend MpfrClass operator* (const MpfrClass& r1, const mpz_srcptr r2) ;
    friend MpfrClass operator* (const MpfrClass& r1, const mpq_srcptr r2) ;
    friend MpfrClass operator* (const double r1, const MpfrClass& r2);
    friend MpfrClass operator* (const int r1, const MpfrClass& r2);
    friend MpfrClass operator* (const unsigned int r1, const MpfrClass& r2);
    friend MpfrClass operator* (const long int r1, const MpfrClass& r2);
    friend MpfrClass operator* (const unsigned long int r1, const MpfrClass& r2);
    friend MpfrClass operator* (const mpz_srcptr r1, const MpfrClass& r2);
    friend MpfrClass operator* (const mpq_srcptr r1, const MpfrClass& r2);
    MpfrClass& operator*= (const MpfrClass& r) ;
    MpfrClass& operator*= (const double r) ;
    MpfrClass& operator*= (const int r) ;
    MpfrClass& operator*= (const unsigned int r) ;
    MpfrClass& operator*= (const long int r) ;
    MpfrClass& operator*= (const unsigned long int r) ;
    MpfrClass& operator*= (const mpz_srcptr r) ;
    MpfrClass& operator*= (const mpq_srcptr r) ;
    static void mul (MpfrClass& res, 
                          const MpfrClass& r1, const MpfrClass& r2,
                          RoundingMode rnd = getDefaultRndMode());

    //static MpfrClass& operator/ (const MpfrClass& r1, const MpfrClass& r2) const;
    MpfrClass operator/ (const MpfrClass& r) const;
    friend MpfrClass operator/ (const MpfrClass& r1, const double r2) ;
    friend MpfrClass operator/ (const MpfrClass& r1, const int r2) ;
    friend MpfrClass operator/ (const MpfrClass& r1, const unsigned int r2) ;
    friend MpfrClass operator/ (const MpfrClass& r1, const long int r2) ;
    friend MpfrClass operator/ (const MpfrClass& r1, const unsigned long int r2) ;
    friend MpfrClass operator/ (const MpfrClass& r1, const mpz_srcptr r2) ;
    friend MpfrClass operator/ (const MpfrClass& r1, const mpq_srcptr r2) ;
    friend MpfrClass operator/ (const double r1, const MpfrClass& r2) ;
    friend MpfrClass operator/ (const int r1, const MpfrClass& r2) ;
    friend MpfrClass operator/ (const unsigned int r1, const MpfrClass& r2) ;
    friend MpfrClass operator/ (const long int r1, const MpfrClass& r2) ;
    friend MpfrClass operator/ (const unsigned long int r1, const MpfrClass& r2) ;
    friend MpfrClass operator/ (const mpz_srcptr r1, const MpfrClass& r2) ;
    friend MpfrClass operator/ (const mpq_srcptr r1, const MpfrClass& r2) ;
    MpfrClass& operator/= (const MpfrClass& r) ;
    MpfrClass& operator/= (const double r) ;
    MpfrClass& operator/= (const int r) ;
    MpfrClass& operator/= (const unsigned int r) ;
    MpfrClass& operator/= (const long int r) ;
    MpfrClass& operator/= (const unsigned long int r) ;
    MpfrClass& operator/= (const mpz_srcptr r) ;
    MpfrClass& operator/= (const mpq_srcptr r) ;
    static void div (MpfrClass& res, 
                          const MpfrClass& r1, const MpfrClass& r2,
                          RoundingMode rnd = getDefaultRndMode());

    static void fma (MpfrClass& res, 
                          const MpfrClass& r1, const MpfrClass& r2,
                          const MpfrClass& r3, 
                          RoundingMode rnd = getDefaultRndMode());


    // Input/Output
    std::ostream& put(std::ostream& o,
                 RoundingMode rnd = getDefaultRndMode(),
                 PrecisionType prec = getDefaultPrecision(),
                 int base = 10,
                 int nb_digits = 0) const;
                 //PrecisionType prec = PrecisionType(0) ) const;
    friend std::istream& operator >> (std::istream &i, MpfrClass& r);
    friend std::ostream& operator << (std::ostream &o, const MpfrClass& r);



    // Mathematical functions: exp, sin...
    void random (PrecisionType prec = getDefaultPrecision());

    friend MpfrClass abs (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass agm (const MpfrClass& r1, const MpfrClass& r2, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass sqrt (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());

    friend MpfrClass exp (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass expm1 (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass exp2 (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass log (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass log2 (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass log10 (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass log1p (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());

    friend MpfrClass sin (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass cos (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend void sin_cos (MpfrClass& res_sin, MpfrClass& res_cos,
                        const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass tan (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
  
    friend MpfrClass acos (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass asin (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass atan (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
  
    friend MpfrClass cosh (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass sinh (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass tanh (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
  
    friend MpfrClass atanh (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass acosh (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass asinh (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
  
    MpfrClass pow (const unsigned long int e, RoundingMode rnd = MpfrClass::getDefaultRndMode()) const;
    MpfrClass pow (const long int e, RoundingMode rnd = MpfrClass::getDefaultRndMode()) const;
    MpfrClass pow (const MpfrClass& e, RoundingMode rnd = MpfrClass::getDefaultRndMode()) const;
    friend MpfrClass power(const MpfrClass & x, const MpfrClass &e) 
    { return x.pow(e, MpfrClass::getDefaultRndMode()); }
    friend MpfrClass power(const MpfrClass & x, const long int e) 
    { return x.pow(e, MpfrClass::getDefaultRndMode()); }
    
    friend MpfrClass cbrt (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass gamma (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass erf (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass factorial (const unsigned long int e, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass hypot (const MpfrClass& r1, const MpfrClass& r2, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass zeta (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    //end mathematical functions


    // The four rounding modes as in IEEE-754 arithmetic and the fractional part
    friend MpfrClass round (const MpfrClass& r);
    friend MpfrClass floor (const MpfrClass& r);
    friend MpfrClass trunc (const MpfrClass& r);
    friend MpfrClass ceil (const MpfrClass& r);
    friend MpfrClass frac (const MpfrClass& r);

    friend long int toInt (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend unsigned long int toUInt (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend double toDouble (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend long double toLDouble (const MpfrClass& r, RoundingMode rnd = MpfrClass::getDefaultRndMode());
    MpfrClass leftBound()
    { return *this; }
    MpfrClass rightBound()
    { return *this; }
    bool contains(const MpfrClass & X)
    { return (mpfr_cmp(mpfr_rep,X.mpfr_rep)==0); }
    bool containsInInterior(const MpfrClass & X)
    { return false; }

    friend MpfrClass relDiff (const MpfrClass& r1, const MpfrClass& r2, 
                              RoundingMode rnd = MpfrClass::getDefaultRndMode());
    friend MpfrClass nextAbove (const MpfrClass& r);
    friend MpfrClass nextBelow (const MpfrClass& r);
    friend MpfrClass nextToward (const MpfrClass& r, const MpfrClass& dir);
    
};


//--------------------------
// Comparison operators
//--------------------------
bool operator == (const MpfrClass& r1, const MpfrClass& r2);
bool operator == (const MpfrClass& r1, const double r2);
bool operator == (const MpfrClass& r1, const int r2);
bool operator == (const MpfrClass& r1, const unsigned int r2);
bool operator == (const MpfrClass& r1, const long int r2);
bool operator == (const MpfrClass& r1, const unsigned long int r2);
bool operator == (const double r1, const MpfrClass& r2);
bool operator == (const int r1, const MpfrClass& r2);
bool operator == (const unsigned int r1, const MpfrClass& r2);
bool operator == (const long int r1, const MpfrClass& r2);
bool operator == (const unsigned long int r1, const MpfrClass& r2);

bool operator != (const MpfrClass& r1, const MpfrClass& r2);
bool operator != (const MpfrClass& r1, const double r2);
bool operator != (const MpfrClass& r1, const int r2);
bool operator != (const MpfrClass& r1, const unsigned int r2);
bool operator != (const MpfrClass& r1, const long int r2);
bool operator != (const MpfrClass& r1, const unsigned long int r2);
bool operator != (const double r1, const MpfrClass& r2);
bool operator != (const int r1, const MpfrClass& r2);
bool operator != (const unsigned int r1, const MpfrClass& r2);
bool operator != (const long int r1, const MpfrClass& r2);
bool operator != (const unsigned long int r1, const MpfrClass& r2);

bool operator <  (const MpfrClass& r1, const MpfrClass& r2);
bool operator <  (const MpfrClass& r1, const double r2);
bool operator <  (const MpfrClass& r1, const int r2);
bool operator <  (const MpfrClass& r1, const unsigned int r2);
bool operator <  (const MpfrClass& r1, const long int r2);
bool operator <  (const MpfrClass& r1, const unsigned long int r2);
bool operator <  (const double r1, const MpfrClass& r2);
bool operator <  (const int r1, const MpfrClass& r2);
bool operator <  (const unsigned int r1, const MpfrClass& r2);
bool operator <  (const long int r1, const MpfrClass& r2);
bool operator <  (const unsigned long int r1, const MpfrClass& r2);

bool operator <= (const MpfrClass& r1, const MpfrClass& r2);
bool operator <= (const MpfrClass& r1, const double r2);
bool operator <= (const MpfrClass& r1, const int r2);
bool operator <= (const MpfrClass& r1, const unsigned int r2);
bool operator <= (const MpfrClass& r1, const long int r2);
bool operator <= (const MpfrClass& r1, const unsigned long int r2);
bool operator <= (const double r1, const MpfrClass& r2);
bool operator <= (const int r1, const MpfrClass& r2);
bool operator <= (const unsigned int r1, const MpfrClass& r2);
bool operator <= (const long int r1, const MpfrClass& r2);
bool operator <= (const unsigned long int r1, const MpfrClass& r2);

bool operator >  (const MpfrClass& r1, const MpfrClass& r2);
bool operator >  (const MpfrClass& r1, const double r2);
bool operator >  (const MpfrClass& r1, const int r2);
bool operator >  (const MpfrClass& r1, const unsigned int r2);
bool operator >  (const MpfrClass& r1, const long int r2);
bool operator >  (const MpfrClass& r1, const unsigned long int r2);
bool operator >  (const double r1, const MpfrClass& r2);
bool operator >  (const int r1, const MpfrClass& r2);
bool operator >  (const unsigned int r1, const MpfrClass& r2);
bool operator >  (const long int r1, const MpfrClass& r2);
bool operator >  (const unsigned long int r1, const MpfrClass& r2);

bool operator >= (const MpfrClass& r1, const MpfrClass& r2);
bool operator >= (const MpfrClass& r1, const double r2);
bool operator >= (const MpfrClass& r1, const int r2);
bool operator >= (const MpfrClass& r1, const unsigned int r2);
bool operator >= (const MpfrClass& r1, const long int r2);
bool operator >= (const MpfrClass& r1, const unsigned long int r2);
bool operator >= (const double r1, const MpfrClass& r2);
bool operator >= (const int r1, const MpfrClass& r2);
bool operator >= (const unsigned int r1, const MpfrClass& r2);
bool operator >= (const long int r1, const MpfrClass& r2);
bool operator >= (const unsigned long int r1, const MpfrClass& r2);

MpfrClass min (const MpfrClass& a, const MpfrClass& b);
MpfrClass max (const MpfrClass& a, const MpfrClass& b);

inline MpfrClass right(const MpfrClass& x){
  return x;
}

inline MpfrClass left(const MpfrClass& x){
  return x;
}

inline MpfrClass mid(const MpfrClass& x){
  return x;
}

inline MpfrClass nonnegativePart(const MpfrClass& x)
{
  return abs(x);
}

}}  // end of namespace capd::multiPrec

#include "capd/multiPrec/MpfrClass_inline.h"

#endif  // USE_OLD_MPFRCLASS


#endif // _CAPD_MULTIPREC_MPFRCLASS_H_ 

#endif   // __HAVE_MPFR__


