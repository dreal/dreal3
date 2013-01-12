//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file MpInt.h
///
///  Defines C++ wrapper for multiple precision integers
///  from gmpxx library
///
/// @author Tomasz Kapela   @date 2010-03-08
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

// Protects against compilations in systems without mpfr and gmp package
#ifdef __HAVE_MPFR__

#ifndef _CAPD_MULTIPREC_MPINT_H_
#define _CAPD_MULTIPREC_MPINT_H_


#include <gmpxx.h>

namespace capd{
namespace multiPrec{

typedef mpz_class MpInt;


}} // end of namespace capd::multiPrec

inline capd::multiPrec::MpInt power(const capd::multiPrec::MpInt & base, int exp){
  capd::multiPrec::MpInt result;
  mpz_pow_ui(result.get_mpz_t(), base.get_mpz_t(), exp);
  return result;
}

inline capd::multiPrec::MpInt nonnegativePart(const capd::multiPrec::MpInt & x) {
  if(x>=0)
    return x;
  else
    throw "non negative part is empty!";
}
#include "capd/auxil/minmax.h"
namespace capd{
template<>
inline capd::multiPrec::MpInt abs(const capd::multiPrec::MpInt & x) {
  return ::abs(x);
}
}
#endif // _CAPD_MULTIPREC_MPINT_H_

#endif   // __HAVE_MPFR__


