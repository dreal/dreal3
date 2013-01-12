//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD
//   Subpackage:
/// @addtogroup intervals
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file DoubleInterval.cpp
///
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <cmath>

#include "capd/rounding/DoubleRounding.h"

#include "capd/intervals/DoubleInterval.h"

#include "capd/intervals/Interval.hpp"

using std::log;

typedef capd::rounding::DoubleRounding DoubleRounding;

template class capd::intervals::Interval<double, DoubleRounding>;

// deprecated
interval pi = interval::pi();

namespace capd{
namespace intervals{

template DoubleInterval diam<double, DoubleRounding>(const DoubleInterval& );
template bool  intersection<double, DoubleRounding>( DoubleInterval A_iv1,
                    DoubleInterval A_iv2,
                    DoubleInterval &A_rIntersection);
template DoubleInterval intervalHull<double, DoubleRounding>(const DoubleInterval & A_iv1,
                                                                        const DoubleInterval & A_iv2);
template void split<double, DoubleRounding>( DoubleInterval & A_iv, DoubleInterval & A_rMid,
                                                              double & A_diam);
template DoubleInterval power<double, DoubleRounding> (const DoubleInterval & x, int n);
template DoubleInterval power <double, DoubleRounding>(const DoubleInterval & a,
                                                                  const DoubleInterval & b);
template DoubleInterval sqrt <double, DoubleRounding>(const DoubleInterval &x);
template DoubleInterval sin <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval cos <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval tan <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval cot <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval atan <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval asin <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval acos <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval sinh <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval cosh <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval tanh <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval coth <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval exp <double, DoubleRounding>(const DoubleInterval & x);
template DoubleInterval log <double, DoubleRounding>(const DoubleInterval& x);
template DoubleInterval solveAffineInclusion<double, DoubleRounding>(const DoubleInterval & a,
                                               const DoubleInterval & p,
                                               const DoubleInterval & c);
template DoubleInterval solveAffineInclusion<double, DoubleRounding>(const DoubleInterval & a,
                                               const DoubleInterval & p,
                                               const DoubleInterval & c,
                                               int & dir);
 
//////////////////////////////////////////////////////////////////////////
//         Arithmetic operators
//////////////////////////////////////////////////////////////////////////
#ifndef __INTERVAL_SPEED_OPTIMIZED__

template DoubleInterval operator +<double, DoubleRounding>(const DoubleInterval & A_iv1, const DoubleInterval & A_iv2);
template  DoubleInterval operator -<double, DoubleRounding>(const DoubleInterval & A_iv1, const DoubleInterval & A_iv2);
template DoubleInterval  operator *<double, DoubleRounding>(const DoubleInterval & A_iv1,
                                      const DoubleInterval & A_iv2);
template DoubleInterval operator /<double, DoubleRounding>(const DoubleInterval & A_iv1,
                                     const DoubleInterval & A_iv2);
template std::ostream & operator << <double, DoubleRounding>(std::ostream & s,
                                   const DoubleInterval & A_iv);
template std::istream &operator>> <double, DoubleRounding>(std::istream &inp, DoubleInterval &i);
template DoubleInterval add<double, DoubleRounding>(const DoubleInterval & A_iv, const double & A_x);
template DoubleInterval substract<double, DoubleRounding>(const DoubleInterval & A_iv, const double &A_x);
template DoubleInterval substract<double, DoubleRounding>(const double  &A_x, const DoubleInterval & A_iv);
template DoubleInterval multiply<double, DoubleRounding>(const DoubleInterval & A_iv, const double & A_x);
template DoubleInterval divide<double, DoubleRounding>(const DoubleInterval & A_iv,
                                            const double & A_x);
template  DoubleInterval divide<double, DoubleRounding>(const double & A_x, const DoubleInterval & A_iv);


#endif  //__INTERVAL_SPEED_OPTIMIZED__
}}  // end of namespace capd::intervals
											   
/// @}

