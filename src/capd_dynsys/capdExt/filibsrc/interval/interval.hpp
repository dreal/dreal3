/*                                                                           
**  fi_lib++  --- A fast interval library (Version 2.0)                     
**                                                                  
**  Copyright (C) 2001:                                                        
**                                                     
**  Werner Hofschuster, Walter Kraemer                               
**  Wissenschaftliches Rechnen/Softwaretechnologie (WRSWT)  
**  Universitaet Wuppertal, Germany                                           
**  Michael Lerch, German Tischler, Juergen Wolff von Gudenberg       
**  Institut fuer Informatik                                         
**  Universitaet Wuerzburg, Germany                                           
** 
**  This library is free software; you can redistribute it and/or
**  modify it under the terms of the GNU Library General Public
**  License as published by the Free Software Foundation; either
**  version 2 of the License, or (at your option) any later version.
**
**  This library is distributed in the hope that it will be useful,
**  but WITHOUT ANY WARRANTY; without even the implied warranty of
**  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
**  Library General Public License for more details.
**
**  You should have received a copy of the GNU Library General Public
**  License along with this library; if not, write to the Free
**  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA
*/
#if ! defined(INTERVAL)
#define INTERVAL

#include <stdexcept>
#include <iostream>
#include <string>
#include <cmath>
#include <functional>
#include <algorithm>
#include <exception>

#include <fp_traits/fp_traits.hpp>
#include <ieee/primitive.hpp>
 
namespace filib
{
	/**
	 * interval computation mode
	 **/
	enum interval_mode
	{
		i_mode_normal = 0,
		i_mode_extended = 1,
		i_mode_extended_flag = 2
	};

	template <typename N, rounding_strategy K, interval_mode E>
	class interval;

	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator+  (
		interval<N,K,E> const & a,
		interval<N,K,E> const & b);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator+  (
		interval<N,K,E> const & a,
		N const & b);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator+  (
		N const & b,
		interval<N,K,E> const & a);

	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator-  (
		interval<N,K,E> const & a, 
		interval<N,K,E> const & b);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator-  (
		interval<N,K,E> const & a, 
		N const & b);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator-  (
		N const & b,
		interval<N,K,E> const & a);

	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> cancel (
		interval<N,K,E> const & a, 
		interval<N,K,E> const & b);

	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator*  (
		interval<N,K,E> const & a,
		interval<N,K,E> const & b);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator*  (
		interval<N,K,E> const & a,
		N const & b);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator*  (
		N const & b,
		interval<N,K,E> const & a);
		
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator/  (
		interval<N,K,E> const & a,
		interval<N,K,E> const & b);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator/  (
		interval<N,K,E> const & a,
		N const & b);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> operator/  (
		N const & b,
		interval<N,K,E> const & a);

	/**
	 inf(a) == a.inf()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N const & inf (interval<N,K,E> const &);
	/**
	 sup(a) == a.sup()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N const & sup (interval<N,K,E> const &);
	/**
	 inf(a) == a.inf()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N inf_by_value (interval<N,K,E> const &);
	/**
	 sup(a) == a.sup()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N sup_by_value (interval<N,K,E> const &);
	/**
	 isPoint(a) == a.isPoint()
	 */
	template < typename N, rounding_strategy K, interval_mode E > bool isPoint (interval<N,K,E> const &);	
	
	/**
	 isInfinite(a) == a.isInfinite()
	 */
	template < typename N, rounding_strategy K, interval_mode E > bool isInfinite (interval<N,K,E> const &);
	/**
	 isInfinite(a) == a.isInfinite()
	 */
	template < typename N, rounding_strategy K, interval_mode E > bool isEmpty (interval<N,K,E> const &);			
	
	/**
	 hasUlpAcc(a,n) == a.hasUlpAcc(n)
	 */
	template < typename N, rounding_strategy K, interval_mode E > bool hasUlpAcc (interval<N,K,E> const &, unsigned int const &);
	/**
	 mid(a) == a.mid()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N mid(interval<N,K,E> const &);
	/**
	 diam(a) == a.diam()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N diam(interval<N,K,E> const &);
	template < typename N, rounding_strategy K, interval_mode E > N width(interval<N,K,E> const &);
	/**
	 relDiam(a) == a.relDiam()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N relDiam(interval<N,K,E> const &);
	/**
	 rad(a) == a.rad()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N rad(interval<N,K,E> const &);
	/**
	 mig(a) == a.mig()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N mig(interval<N,K,E> const &);
	/**
	 mag(a) == a.mag()
	 */
	template < typename N, rounding_strategy K, interval_mode E > N mag(interval<N,K,E> const &);
	/**
	 same as a.abs()
	 */
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> abs(interval<N,K,E> const &);
	/**
	 Same as x.imin(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> imin(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.imax(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> imax(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.dist(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E > N dist(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.blow(eps)
	*/
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E> blow(interval<N,K,E> const & x, N const & eps);
	/**
	 Same as x.intersect(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E>
	intersect(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.hull(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E>
	hull(interval<N,K,E> const & x, interval<N,K,E> const & y);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E>
	interval_hull(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as y.hull(x)
	*/
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E>
	hull(N const & x, interval<N,K,E> const & y);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E>
	interval_hull(N const & x, interval<N,K,E> const & y);
	/**
	 Returns the convex hull of two double numbers x and y.

	 Special cases in the extended system:
	 <UL>
	 <LI> hull(x, y) == [ EMPTY ] for x == y == NaN
	 </UL>
	*/
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E>
	hull(N const & x, N const & y);
	template < typename N, rounding_strategy K, interval_mode E > interval<N,K,E>
	interval_hull(N const & x, N const & y);
	/**
	 Same as x.disjoint(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool disjoint(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Returns true iff double number x is contained in interval y
	
	 Special cases in the extended system:
	 <UL>
	 <LI> in(x, y) == false for x == NaN or y == [ EMPTY ]
	 </UL>
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool in(N const & x, interval<N,K,E> const & y);
	/**
	 Same as x.interior(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool interior(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.proper_subset(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool proper_subset(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.subset(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool subset(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Returns true iff interval x is a subset of interval y.
	 @see #subset
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool operator <=(interval<N,K,E> const & x, interval<N,K,E> const & y);
 	/**
	 Same as x.proper_superset(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool proper_superset(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.superset(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool superset(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Returns true iff this interval x is a superset of interval y.
	 @see #superset
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool operator >=(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.seq(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	bool seq(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Returns true iff intervals x and y are set-equal.
	 @see #seq
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool operator ==(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.sne(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool sne(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Returns true iff interval x is set-not-equal to interval y.
	 @see #sne
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool operator !=(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.sge(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool sge(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.sgt(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool sgt(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.sle(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool sle(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.slt(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool slt(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.ceq(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool ceq(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.cne(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool cne(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.cge(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool cge(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.cgt(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool cgt(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.cle(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool cle(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.clt(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool clt(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.peq(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool peq(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.pne(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool pne(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.pge(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool pge(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.pgt(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool pgt(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.ple(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool ple(interval<N,K,E> const & x, interval<N,K,E> const & y);
	/**
	 Same as x.plt(y)
	*/
	template < typename N, rounding_strategy K, interval_mode E >	
	bool plt(interval<N,K,E> const & x, interval<N,K,E> const & y);

	/**
	 overload for stream o
	 */
	template < typename N, rounding_strategy K, interval_mode E >
	std::ostream & operator <<(
		std::ostream & out,
		interval<N,K,E> const & a);
	template < typename N, rounding_strategy K, interval_mode E >
	std::ostream & corebench_out(
		std::ostream & out,
		interval<N,K,E> const & a);
	/**
	 overload for stream i
	 */
	template < typename N, rounding_strategy K, interval_mode E >
	std::istream & operator >>(
		std::istream & out,
		interval<N,K,E> & a)
	throw(interval_io_exception)
	;

	/**
	 Returns an interval enclosure of the inverse cosine of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> acos(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the inverse hyperbolic cosine of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> acosh(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the inverse cotangent of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> acot(interval<N,K,E> const & x);
  
	/**
	 Returns an interval enclosure of the inverse hyperbolic cotangent of 
	 the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> acoth(interval<N,K,E> const & x);
  
	/**
	 Returns an interval enclosure of the inverse sine of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> asin(interval<N,K,E> const & x);
	
	/**
	 Returns an interval enclosure of the inverse hyperbolic sine of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> asinh(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the inverse tangent of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> atan(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the inverse hyperbolic tangent of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> atanh(interval<N,K,E> const & x);
  
	/**
	 Returns an interval enclosure of the cosine of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E>  cos(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the hyperbolic cosine of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> cosh(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the cotangent of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E>  cot(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the hyperbolic cotangent of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> coth(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the exponential of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E>  exp(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the exponential (base 10) of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> exp10(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the exponential (base 2) of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> exp2(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of exp(x)-1
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> expm1(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the natural logarithm of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E>  log(interval<N,K,E> const & x);
  
	/**
	 Returns an interval enclosure of the logarithm (base 10) of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> log10(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of log(1+x).
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> log1p(interval<N,K,E> const & x);
  
	/**
	 Returns an interval enclosure of the logarithm (base 2) of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
#if ! defined(__CYGWIN__)
	interval<N,K,E> log2(interval<N,K,E> const & x);
#else
	interval<N,K,E> log_2(interval<N,K,E> const & x);
#endif

	/**
	 Returns an interval enclosure of x^n.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> pow(interval<N,K,E> const & x, int const &);

	/**
	 Returns an interval enclosure of x^y = exp(y*log(x)).
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> power(interval<N,K,E> const & x, interval<N,K,E> const & y);

	/**
	 Returns an interval enclosure of the sine of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E>  sin(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the hyperbolic sine of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> sinh(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of x^2.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E>  sqr(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the square root of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> sqrt(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the tangent of the interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E>  tan(interval<N,K,E> const & x);

	/**
	 Returns an interval enclosure of the hyperbolic tangent of the 
	 interval x.
	*/
	template < typename N, rounding_strategy K, interval_mode E >
	interval<N,K,E> tanh(interval<N,K,E> const & x);

	/**
	 template interval class
	 
	 template arguments:
	  N: arithmetic type
	  K: see rounding_control
	  E: see interval_mode
	 */
	template <typename N = double, rounding_strategy K = native_switched, interval_mode E = i_mode_normal >
	class interval
	{
		protected:
			/**
			 lower interval limit (infimum)
			 */
			N INF;
			/**
			 upper interval limit (supremum)
			 */
			N SUP;
	
		public:
			typedef N value_type;
			static const rounding_strategy rounding_type = K;
			typedef fp_traits<N,K> traits_type;

			static bool extended_error_flag;

			static bool getExtendedErrorFlag() 
			{
				return extended_error_flag;
			}
			static void resetExtendedErrorFlag()
			{
				extended_error_flag = false;
			}

			static inline interval<N,K,E> constructIntervalNoChecks(N const & rl, N const & ru)
			{
				interval<N,K,E> I;
				I.INF = rl;
				I.SUP = ru;
				return I;
			}
			
			inline interval<N,K,E> uncheckedIntersect(N const & rl, N const & ru) const
			{
				interval<N,K,E> domain = constructIntervalNoChecks(rl,ru);
				return intersect(domain);
			}                       

			/**
			 provided for internal reasons,
			 speed up construction where we don't
			 need the usual sanity checks
			 */
			inline explicit interval(
				N const & rl, N const & ru, char const &);

			inline interval(
				std::string const & infs, std::string const & sups)
			throw(interval_io_exception);

			/**
			 check for infinity (?)
			 */
			inline void checkInf();

			/**
			 default constructor,
			 don't use it if you are not the STL
			 */
			inline interval();

			/**
			 constructor for point interval
			 rp: point
			 */
			inline interval(N const & rp);

			/**
			 constructor by values
			 rl: infimum
			 ru: supremum
			 */
			inline interval(N const & rl, N const & ru);

			/**
			 copy constructor
			 */
			inline interval(interval<N,K,E> const & o);

			/**
			 destructor
			 */
			inline ~interval();

			/**
			 assignment operator
			 */
			inline interval<N,K,E> & operator= (interval<N,K,E> const & o);

			/**
			 unary operator +
			 */
			inline interval<N,K,E> const & operator+() const;

			/**
			 unary operator -
			 */
			inline interval<N,K,E> operator-() const;

			/**
			 return infimum
			 */
			inline N const & inf() const;

			/**
			 return supremum
			 */
			inline N const & sup() const;

			/**
			 unary +=
			 */
			inline interval<N,K,E> & operator +=(interval<N,K,E> const & o);

			/**
			 unary += for number
			 */
			inline interval<N,K,E> & operator +=(N const & a);

			/**
			 unary -=
			 */
			inline interval<N,K,E> & operator -=(interval<N,K,E> const & o);

			/**
			 unary -= for number
			 */
			inline interval<N,K,E> & operator -=(N const & a);

			/**
			 unary operator*=
			 */
			inline interval<N,K,E> & operator *= (interval<N,K,E> const & a);

			/**
			 unary operator *= for point
			 */
			inline interval<N,K,E> & operator *=(N const & a);

			/**
			 unary operator /=
			 */
			inline interval<N,K,E> & operator /= (interval<N,K,E> const & a);
			/**
			 unary operator /= for point
			 */
			inline interval<N,K,E> & operator/= (N const & a);

			/**
			 is this interval empty ?	
			 */
			inline bool isEmpty() const;
			inline bool isInfinite() const;
			static inline interval<N,K,E> EMPTY();
			static inline interval<N,K,E> ENTIRE();
			static inline interval<N,K,E> NEG_INFTY();
			static inline interval<N,K,E> POS_INFTY();

			static inline interval<N,K,E> ZERO();
			static inline interval<N,K,E> ONE();
			static inline interval<N,K,E> PI();

			inline bool isPoint() const;

			/**
			 Returns true iff this interval has an ulp accuracy of n, i.e. a.inf()
			 and a.sup() have a distance of at most n machine numbers.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.hasUlpAcc(n) == false for x == [ EMPTY ] or any infinite interval
			 </UL>
 			 */
			bool hasUlpAcc(unsigned int const & n) const;
			/**
			 true <-> defined(FILIB_EXTENDED)
			 */
			static bool isExtended();

			/**
			 Returns an approximation of the midpoint of this interval, i.e.
			
			 x.mid == (x.inf() + x.sup()) / 2.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.mid() == NaN for x == [ EMPTY ]
			 <LI> x.mid() == 0.0 for x == [ ENTIRE ]
			 <LI> x.mid() == +INF for x == [ +INF ] or x = [ a, +INF ]
			 <LI> x.mid() == -INF for x == [ -INF ] or x = [ -INF, a]
			 </UL>
			*/
			N mid() const;
 			/**
			 Returns an upper bound for the diameter (width) of this interval, i.e.
			
			 a.diam() == a.sup()-a.inf()
			
			 Special cases in the extended system:
			 <UL>
			 <LI> a.diam() == NaN for a == [ EMPTY ]
			 <LI> a.diam() == +INF for any infinite interval
			 </UL>
			*/
			N diam() const;
			N width() const;

			/**
			 Returns an upper bound for the relative diameter (width) of this
			 interval, i.e.
			
			 a.relDiam == a.diam() if a.mig() is less than the smallest normalized
			 number
			
			 a.relDiam == a.diam() / a.mig() else
			
			 Special cases in the extended system:
			 <UL>
			 <LI> a.relDiam() == NaN for a == [ EMPTY ]
			 <LI> a.relDiam() == +INF for any infinite interval
			 </UL>			
			*/
			N relDiam() const;

			/**
			 Returns an upper bound for the radius of this interval, i.e.
			
			 a.rad() = (a.sup() - a.inf()) / 2
			
			 Special cases in the extended system:
			 <UL>
			 <LI> a.rad() == NaN for a == [ EMPTY ]
			 <LI> a.rad() == +INF for any infinite interval
			 </UL>
			*/
			N rad() const;

			/**
			 Returns the mignitude of this interval, i.e.
			
			 a.mig() == min{abs(y) : y in x }
			
			 Special cases in the extended system:
			 <UL>
			 <LI> a.mig() == NaN for a == [ EMPTY ]
			 </UL>
			*/
			N mig() const;

			/**
			 Returns the magnitude of this interval, i.e.
			
			 a.mag() == max{abs(y) : y in a }
			
			 Special cases in the extended system:
			 <UL>
			 <LI> a.mag() == NaN for a == [ EMPTY ]
			 <LI> a.mag() == +INF for any infinite interval
			 </UL>
			*/
			N mag() const;

 			/**
			 Returns the interval of absolute values of this interval, i.e.
			
			 a.abs() == [ a.mig(), a.mag() ]
			
			 Special cases in the extended system:
			 <UL>
			 <LI> a.abs() == [ EMPTY ] for a == [ EMPTY ]
			 <LI> a.abs() == [ +INF ] for a == [ +/- INF ]
			 </UL>
			*/
			interval<N,K,E> abs() const;

			/**
			 Returns an enclosure for the range of minima of this interval and the
			 interval x, i.e.
			
			 x.min(y) == { z : z == min(a, b) : a in x, b in y }
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.min(y) == [ EMPTY ] for x == [ EMPTY ] and y == [ EMPTY ]
			 </UL>
			*/
			interval<N,K,E> imin(interval<N,K,E> const & x) const;

			/**
			 Returns an enclosure for the range of maxima of this interval and the
			 interval x, i.e.
			
			 x.max(y) == { z : z == max(a, b) : a in x, b in y }
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.max(y) == [ EMPTY ] for x == [ EMPTY ] and y == [ EMPTY ]
			 </UL>
			*/
			interval<N,K,E> imax(interval<N,K,E> const & x) const;

			/**
			 Returns an upper bound for the Hausdorff distance of this interval
			 and the interval x, i.e.
			
			 x.dist(y) == max{ abs(x.inf()-y.inf()), abs(x.sup() - y.sup()) }
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.dist(y) == NaN for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			N dist(interval<N,K,E> const & x) const;

			/**
			 Returns this interval inflated by eps, i.e.
			
			 x.blow(eps) == (1 + eps)*x - eps*x
			*/
			interval<N,K,E> blow(N const & eps) const;

 			/**
			 Returns the intersection of this interval and the interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.intersect(y) == [ EMPTY ] iff x and y are disjoint
			 </UL>
			*/
			interval<N,K,E> intersect(interval<N,K,E> const & x) const;
 
			/**
			 Returns the convex hull of this interval and the interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.hull(y) == [ EMPTY ] for x == y == [ EMPTY ]
			 </UL>
			*/
			interval<N,K,E> hull(interval<N,K,E> const & x) const;
			interval<N,K,E> interval_hull(interval<N,K,E> const & x) const;

			/**
			 Returns the convex hull of this interval and the double x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.hull(y) == [ EMPTY ] for x == [ EMPTY ] and y == NaN
			 </UL>
			*/
			interval<N,K,E> hull(N const & x) const;
			interval<N,K,E> interval_hull(N const & x) const;

			/**
			 Returns true iff this interval and interval x are disjoint., i.e.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.disjoint(y) == true for x or y == [ EMPTY ]
			 </UL>
			*/
			bool disjoint(interval<N,K,E> const & x) const;

			/**
			 Returns true iff double number x is contained in this interval.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.contains(y) == false for x == [ EMPTY ] or y == NaN
			 </UL>
			*/
			bool contains(N x) const;

			/**
			 Returns true iff this interval is in interior of interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.interior(y) == true for x == [ EMPTY ]
			 </UL>
			*/
			bool interior(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is a proper subset of interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.proper_subset(y) == true for x == [ EMPTY ] and y != [ EMPTY ]
			 </UL>
			*/
			bool proper_subset(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is a subset of interval x.
			 Special cases in the extended system:
			
			 <UL>
			 <LI> x.subset(y) == true for x == [ EMPTY ]
			 </UL>
			*/
			bool subset(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is a proper superset of interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.proper_superset(y) == true for x != [ EMPTY ] and y == [ EMPTY ]
			 </UL>
			*/
			bool proper_superset(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is a superset of interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.superset(y) == true for y == [ EMPTY ]
			 </UL>
			*/
			bool superset(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is set-equal to interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.seq(y) == true for x == y == [ EMPTY ]
			 </UL>
			*/
			bool seq(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is set-not-equal to interval x.
			*/
			bool sne(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is set-greater-or-equal to
			 interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.sge(y) == true for x == y == [ EMPTY ]
			 </UL>
			*/
			bool sge(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is set-greater than interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.sgt(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool sgt(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is set-less-or-equal to
			 interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.sle(y) == true for x == y == [ EMPTY ]
			 </UL>
			*/
			bool sle(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is set-less than interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.slt(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool slt(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is certainly-equal to interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.ceq(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool ceq(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is certainly-not-equal to interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.cne(y) == true for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool cne(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is certainly-greater-or-equal to
			 interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.cge(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool cge(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is certainly-greater than interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.cgt(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>a
			*/
			bool cgt(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is certainly-less-or-equal to
			 interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.cle(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool cle(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is certainly-less than interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.clt(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool clt(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is possibly-equal to interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.peq(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool peq(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is possibly-not-equal to interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.pne(y) == true for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool pne(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is possibly-greater-or-equal to
			 interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.pge(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool pge(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is possibly-greater than interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.pgt(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool pgt(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is possibly-less-or-equal to
			 interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.ple(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool ple(interval<N,K,E> const & x) const;

			/**
			 Returns true iff this interval is possibly-less than interval x.
			
			 Special cases in the extended system:
			 <UL>
			 <LI> x.plt(y) == false for x == [ EMPTY ] or y == [ EMPTY ]
			 </UL>
			*/
			bool plt(interval<N,K,E> const & x) const;

			/**
			 print a binary representation of the interval
			 */
			std::ostream & bitImage(std::ostream & os) const;
			/**
			 print a hex representation of the interval
			 */
			std::ostream & hexImage(std::ostream & os) const;

			/**
			 get current output precision
			 */
			static int const & precision();
			/**
			 set output precision and return old precision
			 */
			static int precision (int const &);
			/*
			 amin, compute min(|INF|,|SUP|)
			 */
			inline N amin() const;
			/*
			 amax, compute max(|INF|,|SUP|)
			 */
			inline N amax() const;

			static interval<N,K,E> readBitImage(std::istream &) 
				throw(interval_io_exception);
			static interval<N,K,E> readHexImage(std::istream &) 
				throw(interval_io_exception);
	};

	template <typename N, rounding_strategy K, interval_mode E>
	bool interval<N,K,E>::extended_error_flag = false;
}

#include <interval/tools.icc>
#include <interval/interval.icc>
#include <interval/filib.hpp>
#include <interval/interval_fo.hpp>

#endif
