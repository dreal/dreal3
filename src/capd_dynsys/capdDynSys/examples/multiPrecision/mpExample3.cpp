///////////////////////////////////////////////////////////////////////
//
/// @file mpExample3.cpp
/// Example how to use multiple precision vectors and functions
///
/// @author kapela  @date 2010-01-07
///
// /////////////////////////////////////////////////////////////////////


// Copyright (C) CAPD group
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#include <iostream>
using namespace std;

// symbol __HAVE_MPFR__ is defined if you compile with multiple-precision support (e.g. make target=X11-gmp)
#ifdef __HAVE_MPFR__


#include "capd/multiPrec/MpReal.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/map/Function.hpp"

typedef capd::multiPrec::MpReal          MpFloat;        // multiple-precision floating point number
typedef capd::vectalg::Vector<MpFloat, 0>    MpVector;      // multiple-precision vector
typedef capd::map::Function<MpVector>     MpFunction;       // multiple-precision function

int main(){
  MpFloat::setDefaultPrecision(100);
  /// We set MpFloat to round numbers up in each operation
  MpFloat::setDefaultRndMode(MpFloat::RoundUp);

  MpFloat a(1),
          b("0.1",MpFloat::RoundNearest), // 0.1 is not representable and
	                                          // we want round it to nearest representable
          c(0.125);                      // 0.125 is representable so no rounding needed

  MpVector v(3);
  v[0] = a;  v[1] = b; v[2] = c;
  char formula[] = "var:a,b,c;fun:a+b+c;";
  MpFunction f(formula);
  cout.precision(30);  // 100 mantisa bits correspond to 30 decimal digits
  cout << "\n Function : " << formula
       << "\n argumets : " << v
       << "\n f(a,b,c) = " << f(v) << endl;

  return 0;
}

#else
int main(){
  cout << "This program was compiled without multiple precision support."
       << "\nThe __HAVE_MPFR__ symbol was not defined during compilation "
       << "\n(most probably during CAPD compilation mpfr library was not found)\n    ";
  return 0;
}
#endif

