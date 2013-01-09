/////////////////////////////////////////////////////////////////////////////
/// @addtogroup Interval
/// @{
 
/////////////////////////////////////////////////////////////////////////////
/// @file mpInterval.h
///
/// Multi Precision Interval class
///
/// Required packages to be installed:
///  - GMP - version at least  4.2.1 
///  - MPFR - version at least 1.3.4
/// 
/// This file is now deprecated instead of
///   capd::multiPrec::Interval
/// one should use
///   capd::intervals::Interval<capd::multiPrec::MpfrClass>
///
/// @deprecated
/// 
/// @author Tomasz Kapela   @date 23-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/multiPrec/MpSetting.h"
#ifdef __HAVE_MPFR__

#ifndef _CAPD_MULTIPREC_MPINTERVAL_H_ 
#define _CAPD_MULTIPREC_MPINTERVAL_H_ 

#include <iostream>
#include <sstream>
#include <stdexcept>

#include "capd/multiPrec/MpfrClass.h"
#include "capd/multiPrec/MpRounding.h"
#ifdef USE_OLD_MPFRCLASS
namespace capd{
namespace multiPrec{
   
/////////////////////////////////////////////////////////////////////////////
// Interval
///
///   Multi Precision Interval class
///
///   @author Tomasz Kapela     @date 22-08-2006
/////////////////////////////////////////////////////////////////////////////
class Interval{

public:
   typedef MpfrClass BoundType;
   
   Interval() {}
   Interval(const BoundType &_value); 
   Interval(const BoundType &_left, const BoundType &_right);
   Interval(const Interval& iv);
   Interval(double _value);
   Interval(double _left, double _right);
   
   Interval& operator = (const Interval& iv);
   Interval& operator +=(const Interval& iv);
   Interval& operator -=(const Interval& iv);
   Interval& operator *=(const Interval& iv);
   Interval& operator /=(const Interval& iv);  
   
   
   friend bool operator ==  (const Interval & iv1, const Interval & iv2);
   friend bool operator <= (const Interval& iv1, const Interval& iv2);
   friend bool operator >= (const Interval& iv1, const Interval& iv2);
   friend bool operator <  (const Interval& iv1, const Interval& iv2);
   friend bool operator >  (const Interval& iv1, const Interval& iv2);
   friend bool operator != (const Interval& iv1, const Interval& iv2);
   
   
   bool contains(const BoundType &x) const;
   bool subset(const Interval &iv) const;
   bool subsetInterior(const Interval &iv) const;
   void split(Interval &r);
   Interval mid(void) const;
   
   friend bool in(const BoundType &_value,const Interval & iv);  // inclusion
   friend bool in (const Interval& small_iv ,const Interval& iv,int interior);// inclusion   
   
   friend inline bool iszero(const Interval& r) { return (iszero(r.left) && iszero(r.right));  }
   friend inline bool isinf(const Interval& r) { return (isinf(r.left) || isinf(r.right)); }
   friend inline bool isnan(const Interval& r) { return (isnan(r.left) || isnan(r.right)); }
   friend inline bool isnumber(const Interval& r) { return (isnumber(r.left) && isnumber(r.right)); }
   
   
   friend Interval operator - (const Interval& iv);

   friend Interval operator + (const Interval& iv1, const Interval& iv2);
   friend Interval operator + (const Interval& iv, const BoundType& _val);
   friend Interval operator + (const BoundType& _val, const Interval& iv);
   friend Interval operator + (const Interval& iv, double _val);
   friend Interval operator + (double _val, const Interval& iv);
   
   friend Interval operator - (const Interval& iv1, const Interval& iv2);
   friend Interval operator - (const Interval& iv, const BoundType& _val);
   friend Interval operator - (const BoundType& _val, const Interval& iv);
   friend Interval operator - (const Interval& iv, double _val);
   friend Interval operator - (double _val, const Interval & iv);
   
   friend Interval operator * (const Interval& iv1, const Interval& iv2);
   friend Interval operator * (const Interval& iv, const BoundType& _val);
   friend Interval operator * (const BoundType& _val, const Interval& iv);
   friend Interval operator * (const Interval& iv, double _val);
   friend Interval operator * (double _val, const Interval& iv);
   
   friend Interval operator / (const Interval& iv1, const Interval& iv2);
 
   friend Interval operator ^ (const Interval& iv1, const int i);
  
   friend Interval sin (const Interval& x);
   friend Interval cos (const Interval& x);
   friend Interval tan (const Interval& x);
   friend Interval cot (const Interval& x);
   friend Interval sinh (const Interval& x);
   friend Interval cosh (const Interval& x);
   friend Interval tanh (const Interval& x);
   friend Interval coth (const Interval& x);
   friend Interval exp (const Interval & x);
   friend Interval log (const Interval& x);

   friend Interval power (const Interval&, long int);
   friend Interval power (const Interval&, const Interval&);
   friend Interval sqrt (const Interval&);
 
   friend Interval intervalHull(const Interval & i1, const Interval & i2);
   friend void splitInterval(Interval& i, Interval::BoundType & diam); 
   friend Interval solveAffineInclusion(const Interval &a, const Interval & p, const Interval& c);
   friend Interval solveAffineInclusion(const Interval &a, const Interval & p, const Interval& c, int &dir);

   
   const BoundType& leftBound() const {return left;}
   const BoundType& rightBound() const {return right;}
   
   // DEPRECATED
   const BoundType& left_b(void) const { return left; }
   const BoundType& right_b(void) const { return right; }

   friend Interval left (const Interval &iv);
   friend Interval right (const Interval &iv);

   friend Interval diam(const Interval &iv);
   friend Interval nonnegativePart(const Interval &iv);

   friend Interval mid(const Interval &iv);                         ///< the middle point of an interval
   friend Interval ball(const Interval &iv, const Interval &r);     ///< ball with center iv and radius r
   
   friend std::ostream& operator<< (std::ostream &stream, const Interval & iv);
  // friend std::istream& operator>>(std::istream &stream, Interval& iv);
   
  // "Constants" (but they depend on the precision)
  static Interval Pi( BoundType::PrecisionType prec = 0);
  static Interval Log2( BoundType::PrecisionType prec = 0);
  static Interval Euler( BoundType::PrecisionType prec = 0);

protected:
   BoundType  left;     ///< left end of the interval
   BoundType  right;    ///< right end of the interval
};

// DEPRECATED FUNCTIONS 
 inline void iSplit(Interval* iv, Interval::BoundType* diam)
 {
    splitInterval(*iv, *diam); 
 }
 inline Interval Ihull(const Interval& i1, const Interval& i2)
 {
    return intervalHull(i1, i2);
 }
 int  intersection(const Interval& x1, const Interval& x2, Interval& cp);
// on output:  if common part of <x1> and <x2> is nonempty then
//                cp =intersection of <x1> and <x2>
//                 and 1 is returned
//              otherwise 0 is returned and cp is untouched 
 
inline bool Degenerate(Interval &iv)
{
   return iv.contains(0.0);
}

}}  // end of namespace capd::multiPrec

 // Definitions of 'inline' functions
#include "capd/multiPrec/MpInterval.hpp"

#endif // OLD_MPFR
#endif // _CAPD_MULTIPREC_MPINTERVAL_H_ 

#endif  // __HAVE_MPFR__

/// @}
