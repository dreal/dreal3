
/////////////////////////////////////////////////////////////////////////////
/// @file mpExample2.cpp
/// Example how to use intervals with multiple precision endpoints
///
/// @author kapela  @date 2010-01-07
///
// ///////////////////////////////////////////////////////////////////////////

// Copyright (C) CAPD group
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#include <iostream>
using namespace std;

// symbol __HAVE_MPFR__ is defined if you compile with multiple-precision support (e.g. make target=X11-gmp)
#ifdef __HAVE_MPFR__

// definition of an interval with multiple-precision end points
#include "capd/interval/MpInterval.h"
#include "capd/multiPrec/MpReal.h"
typedef capd::multiPrec::MpReal          MpFloat;        // multiple-precision floating point number
typedef capd::intervals::Interval<MpFloat>  MpInterval;     // interval with MpFloat endpoints

int main(){
  MpFloat::setDefaultPrecision(200);

  MpFloat a = 1,
          b("0.1",MpFloat::RoundDown),  // 0.1 is not representable so we round down
	                                        // to use it as left endpoint
          c(0.5);                      // 0.5 is representable so no rounding needed
  MpInterval  ia(a),
              ib(b,c),
              ic("-1.2345678901234567890","2020.202020202020202002");
  cout.precision(60);
  cout << "\n ia = " << ia << "\n ib = " << ib << "\n ic = " << ic << endl;

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

