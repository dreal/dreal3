/// @addtogroup capd
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file factrial.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_CAPD_FACTRIAL_H_ 
#define _CAPD_CAPD_FACTRIAL_H_ 

long factorial(long n);        // compute and store n factorial
long newton(long n, long k);   // compute and store newton symbol (n \over k)

namespace capd{

template <long N, long K>
struct Binomial
{
   static const long value = Binomial<N-1,K-1>::value + Binomial<N-1,K>::value;
};

template <long K>
struct Binomial<0,K>
{
   static const long value = 0;
};

template <long N>
struct Binomial<N,0>
{
   static const long value = 1;
};

template<long N>
struct Binomial<N,N>
{
   static const long value=1;
};

template <>
struct Binomial<0,0>
{
   static const long value = 1;
};

template<long N>
struct Factorial
{
   static const long value = N*Factorial<N-1>::value;
};

} // namespace capd

#endif // _CAPD_CAPD_FACTRIAL_H_ 

/// @}
