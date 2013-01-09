///////////////////////////////////////////////////////////////////////
//
/// @file mpExample4.cpp
/// Example how to use multiple precision library
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

// We include all headers from mpcapd library
// These headers define typedefs for all classes included in mpcapd
// The base type is MpFloat - multi precision floating point number
// If CLASS is name of the template class then the name will be
// - MpCLASS  for "nonrigorous" type
//   e.g. MpInterval, MpVector, MpMatrix, MpFunction, MpMap, MpTaylor etc.
// - MpICLASS for rigorous, interval type
//   e.g. MpIVector, MpIMatrix, MpIFunction, MpIMap, MpITaylor etc.
#include "capd/mpcapdlib.h"
using namespace capd;

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
  cout << "\n v = " << v;

  MpFunction f("var:a,b,c;fun:a+b+c;");
  cout << "\n f(a,b,c) = " << f(v) << endl;

  return 0;
}

#else
int main(){
  cout << "This program was compiled without multiple precision support."
       << "\nThe __HAVE_MPFR__ symbol was not defined during compilation "
       << "\n(most probably you called make without option multiprecision=1)\n    ";
  return 0;
}
#endif

