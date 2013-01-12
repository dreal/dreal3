/////////////////////////////////////////////////////////////////////////////
/// @file doubleFun.h
///
/// This file contains definitions of 'double versions' of functions typical for intervals
///
///  The reason for these definitions is to provide common interface
///  to be used in various templates
///
/// @author Tomasz Kapela   @date 03-10-2007
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006

#include <cmath>

#ifndef _CAPD_CAPD_DOUBLEFUN_H_ 
#define _CAPD_CAPD_DOUBLEFUN_H_ 


inline int toInt(long double d)
{
  return  static_cast<int>(d);
}

inline int toInt(double d)
{
  return  static_cast<int>(d);
}

inline double toDouble(double d)
{
  return d;
}

inline long int toLongInt(long double d)
{
  return static_cast<long int>(d);
}

inline long int toLongInt(double d)
{
  return static_cast<long int>(d);
}

inline bool subset(long double A_small, long double A_big)
{
   return ( A_small == A_big );
}

inline bool subset(double A_small, double A_big)
{
   return ( A_small == A_big );
}

inline bool subsetInterior(long double A_small, long double A_big)
{
   return false;
}

inline bool subsetInterior(double A_small, double A_big)
{
   return false;
}

inline bool isZero(long double x)
{
  return (x==0.0);
}

inline bool isZero(double x)
{
  return (x==0.0);
}

inline bool isSingular(long double x)
{
  return (x==0.0);
}

inline bool isSingular(double x)
{
  return (x==0.0);
}

inline long double left(long double x)
{
  return x;
}

inline double left(double x)
{
  return x;
}

inline long double right(long double x)
{
  return x;
}

inline double right(double x)
{
  return x;
}

inline long double leftBound(long double x)
{
  return x;
}

inline double leftBound(double x)
{
  return x;
}

inline long double rightBound(long double x)
{
  return x;
}

inline double rightBound(double x)
{
  return x;
}

inline long double mid(long double x)
{
  return x;
}

inline double mid(double x)
{
  return x;
}

inline long mid(long x)
{
  return x;
}

inline int Mid( int x)
{
  return x;
}

inline bool isInf(double x)
{
  return std::isinf(x);
}

inline bool isInf(long double x)
{
  return std::isinf(x);
}

inline bool isNaN(double x)
{
  return std::isnan(x);
}

inline bool isNaN(long double x)
{
  return std::isnan(x);
}

#endif // _CAPD_CAPD_DOUBLEFUN_H_ 
