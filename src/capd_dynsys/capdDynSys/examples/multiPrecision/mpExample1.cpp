
/*!
 * @file mpExample1.cpp
 * Example how to use MpReal
 *
 * @author kapela  @date 2010-01-07
 *
 */

// Copyright (C) CAPD group
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.


#include <iostream>
using namespace std;

// symbol __HAVE_MPFR__ is defined if you compile with multiple-precision support (e.g. make target=X11-gmp)
#ifdef __HAVE_MPFR__

/// definition of multiple-precision floating point numbers (MpReal)
#include "capd/multiPrec/MpReal.h"
/// We define shorter names:
typedef capd::multiPrec::MpReal          MpFloat;        // multiple-precision floating point number

int main(){
  /// We set precision to 100 mantisa bits (about 30 decimal digits)
  MpFloat::setDefaultPrecision(100);
  /// We set MpFloat to round numbers to the nearest representable
  MpFloat::setDefaultRndMode(MpFloat::RoundNearest);
  MpFloat a = 1,
      b("1.2345678901234567890123456789"),       // string allows to input any number of digits
      c(1.12112, MpFloat::RoundUp, 10),  // use only 10 mantisa bits and round up the initial value 1.2112
      d(1.234567890123456789),                   // only 15 digits is used to initialize (1.234... is converted to double)
      e(1.234567890123456789L);                  // here we say (L suffix) that parameter is of a long double type
  cout << "\n Precision used (in mantisa bits): " << capd::multiPrec::MpReal::getDefaultPrecision() <<"\n";
  cout.precision(30);
  cout << "\n a = " << a << "\n b = " << b << "\n c = " << c
       << "\n d = " << d << "\n e = " << e << endl;
  return 0;
}

#else
int main(){
  cout << "This program was compiled without multiple precision support."
       << "\nThe __HAVE_MPFR__ symbol was not defined during compilation "
       << "\n(most probably during CAPD compilation mpfr library was not found).\n    ";
  return 0;
}
#endif


