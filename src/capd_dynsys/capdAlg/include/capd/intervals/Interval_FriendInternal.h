/////////////////////////////////////////////////////////////////////////////
/// @file Interval_FriendInternal.h
//
/// Interval Arithmetics - friend functions defined inside Interval class 
//
/// @author Tomasz Kapela   @date 11-01-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 




//////////////////////////////////////////////////////////////////////////
//  RELATIONS between interval and types which can be converted to BoundType 
//////////////////////////////////////////////////////////////////////////


///  operator == (interval, scalar)
friend inline bool operator == (const Interval & A_iVal1, 
                                const T_Bound & A_Val2)
{
  return ((A_iVal1.leftBound() == (A_Val2)) && 
          (A_iVal1.rightBound() == (A_Val2)));
}

///  operator == (scalar, interval)
friend inline bool operator == (const T_Bound & A_Val1,
                                const Interval & A_iVal2)
{
   return ((A_Val1 == A_iVal2.leftBound()) && 
           (A_Val1 == A_iVal2.rightBound()));
}

///  operator !=  (interval, scalar)
friend inline bool operator != (const Interval & A_iVal1, 
                                const T_Bound & A_Val2)
{
  return ((A_iVal1.leftBound() != A_Val2) ||
          (A_iVal1.rightBound() != A_Val2));
}

///  operator !=   (scalar, interval)
friend inline bool operator != (const T_Bound & A_Val1,
                                const Interval & A_iVal2)
{
   return ((A_Val1 != A_iVal2.leftBound()) ||
           (A_Val1 != A_iVal2.rightBound()));
}

///  operator >  (interval, scalar)
friend inline bool operator > (const Interval & A_iVal1, 
                               const T_Bound & A_Val2)
{
   return (A_iVal1.leftBound() > A_Val2);
}

///  operator >   (scalar, interval)
friend inline bool operator > (const T_Bound & A_Val1,
                               const Interval & A_iVal2)
{
   return (A_Val1 > A_iVal2.rightBound());
}

///  operator >= (interval, scalar)
friend inline bool operator >= (const Interval & A_iVal1, 
                                const T_Bound & A_Val2)
{
   return (A_iVal1.leftBound() >= A_Val2);
}

///  operator >=  (scalar, interval)
friend inline bool operator >= (const T_Bound & A_Val1,
                                const Interval & A_iVal2)
{
   return (A_Val1 >= A_iVal2.rightBound());
}

///  operator  < (interval, scalar)
friend inline bool operator < (const Interval & A_iVal1, 
                               const T_Bound & A_Val2)
{
   return (A_iVal1.rightBound() < A_Val2);
}

///  operator  <  (scalar, interval)
friend inline bool operator < (const T_Bound & A_Val1,
                               const Interval & A_iVal2)
{
   return (A_Val1 < A_iVal2.leftBound());
}

/// operator <=  (interval, scalar)
friend inline bool operator <= (const Interval & A_iVal1, 
                                const T_Bound & A_Val2)
{
   return (A_iVal1.rightBound() <= A_Val2);
}

/// operator <=  (scalar, interval)
friend inline bool operator <= (const T_Bound & A_Val1, 
                                const Interval & A_iVal2)
{
   return (A_Val1 <= A_iVal2.leftBound());
}

//////////////////////////////////////////////////////////////////////////
//  ARITHMETIC OPERATORS between interval and BoundType 
//////////////////////////////////////////////////////////////////////////
 
 
/// operator +  (interval, scalar)
friend inline Interval operator+(const Interval & A_iVal, 
                                 const T_Bound &A_x)
{  
  return add(A_iVal, A_x);
}

/// operator + (scalar, interval)
friend inline Interval operator+(const T_Bound & A_x, 
                                 const Interval & A_iVal)
{ 
  return add(A_iVal, A_x);
}

/// operator -  (interval, scalar)
friend inline Interval operator-(const Interval & A_iVal, 
                                 const T_Bound &A_x)
{  
  return substract(A_iVal, A_x);
}
  
/// operator - (scalar, interval)
friend inline Interval operator-(const T_Bound  &A_x, 
                                 const Interval & A_iVal)
{ 
  return substract(A_x, A_iVal);
}
  
/// operator * (interval, scalar)
friend inline Interval operator*(const Interval& A_iVal, 
                                 const T_Bound& A_x)
{
  return multiply(A_iVal, A_x);
}

/// operator * (scalar, interval) 
friend inline Interval operator*(const T_Bound& A_x, 
                                 const Interval& A_iVal)
{
  return multiply(A_iVal, A_x);
}
  
/// operator / (scalar, interval)
friend inline Interval operator/(const T_Bound& A_x, 
                                 const Interval& A_iVal)
{
  return  divide(A_x, A_iVal);
}
  
/// operator / (interval, scalar)
friend inline Interval operator/(const Interval& A_iVal, 
                                 const T_Bound& A_x)
{
  return divide (A_iVal, A_x);
}
