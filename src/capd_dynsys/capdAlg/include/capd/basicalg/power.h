/////////////////////////////////////////////////////////////////////////////
/// @file power.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_CAPD_POWER_H_ 
#define _CAPD_CAPD_POWER_H_ 

#include <cmath>
#include <math.h> // required by the Borland compiler

/// @addtogroup basicalg
/// @{

inline double power(double value, int exponent)
{
   return ::pow(value,exponent);
}

inline long double power(long double value, int exponent)
{
   return ::powl(value,exponent);
}

inline float power(float value, int exponent)
{
   return ::pow(value,exponent);
}

inline double power(int value, int exponent)
{
   return ::pow(static_cast<double> (value),exponent);
}

inline double sqr(double x)
{
  return x*x;
}

inline float sqr(float x)
{
  return x*x;
}

inline long double sqr(long double x)
{
  return x*x;
}

/// @}

#endif // _CAPD_CAPD_POWER_H_ 
