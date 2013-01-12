/**
 *  @file multiprecExample.cpp
 *
 *  you can compile with:
 *    g++ -o multiprecExample -D__HAVE_MPFR__ -s -O2 -Wall -frounding-math -I. -ICAPD_DIR/include  multiprecExample.cpp CAPD_DIR/lib/libcapd.a  -lmpfr -lgmp
 *  where
 *    CAPD_DIR is a root directory of the CAPD library
 *  Created on: 2009-12-01
 *      Author: kapela
 */

#include <iostream>
using namespace std;

// symbol __HAVE_MPFR__ is defined if you compile with multiple-precision support (e.g. make target=X11-gmp)
#ifdef __HAVE_MPFR__

// definition of multiple-precision floating point numbers (MpfrClass)
#include "capd/multiPrec/MpReal.h"
// definition of an interval with multiple-precision end points
#include "capd/intervals/MpInterval.h"

// We define shorter names:
typedef capd::multiPrec::MpReal             MpFloat;        // multiple-precision floating point number
typedef capd::intervals::Interval<MpFloat>  MpInterval;     // interval with MpFloat endpoints

// Now you can use MpFloat and MpInterval exactly in the way you use double and DInterval.

#include "capd/vectalg/Vector.hpp"
#include "capd/map/Function.hpp"

typedef capd::vectalg::Vector<MpFloat, 0>    MpVector;
typedef capd::vectalg::Vector<MpInterval, 0> MpIVector;
typedef capd::map::Function<MpVector>     MpFunction;


int main(){
  // We set precision to 100 mantisa bits (about 30 decimal digits)
  MpFloat::setDefaultPrecision(100);
  // We set MpFloat to round numbers to the nearest representable
  MpFloat::setDefaultRndMode(MpFloat::RoundNearest);
  MpFloat a = 1,
      b("1.2345678901234567890123456789"),       // string allows to input any number of digits
      c(1.12112, MpFloat::RoundUp, 10),  // use only 10 mantisa bits and round up the initial value 1.2112
      d(1.234567890123456789),                   // only 15 digits is used to initialize (1.234... is converted to double)
      e(1.234567890123456789L);                  // here we say (L suffix) that parameter is of a long double type
  cout << "Precision used (in mantisa bits): " << MpFloat::getDefaultPrecision() <<"\n";
  cout << "\n a = " << a << "\n b = " << b << "\n c = " << c << "\n d = " << d << "\n e = " << e ;

  MpVector v(3);
  v[0] = a;  v[1] = b; v[2] = c;
  cout << "\n\n v = " << v;

  MpFunction f("var:a,b,c;fun:a+b+c;");
  cout << "\n f(a,b,c) = " << f(v);

  MpInterval  ia(a),
              ib(b,c),
              ic("-1.2345678901234567890","2020.202020202020202002");
  cout << "\n\n ia = " << ia << "\n ib = " << ib << "\n ic " << ic << "\n";
  return 0;
}
#else
int main(){
  cout << "This program was compiled without multiple precision support."
       << "\nThe __HAVE_MPFR__ symbol was not defined during compilation "
       << "\n(most probably during CAPD compilation mpfr library was not found)\n    ";
}
#endif
