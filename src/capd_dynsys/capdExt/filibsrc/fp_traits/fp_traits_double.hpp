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
#if ! defined(FP_TRAITS_DOUBLE)
#define FP_TRAITS_DOUBLE

/**
  namespace for fast interval arithmetric
 */
namespace filib
{
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif		
	fp_traits_base<double>
	{
		public:
			/**
			 minimum
			 */
			static double const min_val;
			/**
			 maximum
			 */
			static double const max_val;
			/**
			 not a number
			 */
			static double const nan_val;
			/**
			 (positive) infinity
			 */
			static double const inf_val;
			/**
			 negative infinity
			 */
			static double const ninf_val;
			/**
			 value under pi
			 */
			static double const l_pi_val;
			/**
			 value above pi
			 */
			static double const u_pi_val;

			/**
			 is double negative ?
			 */
			static inline bool sign(double const &) ;
			/**
			 is double an invalid number
			 */
			static inline bool IsNaN(double const &) ;
			/**
			 is double infinite
			 */
				static inline bool IsInf(double const &) ;
			/**
			 return positive infinity
			 */
			static inline double const & infinity() ;
			/**
			 return negative infinity
			 */
			static inline double const & ninfinity() ;
			/**
			 return quiet NaN
			 */
			static inline double const & quiet_NaN() ;
			/**
			 return value below pi
			 */
			static inline double const & l_pi() ;
			/**
			 return value above pi
			 */
			static inline double const & u_pi() ;
			/**
			 return min
			 */
			static inline double const & min() ;
			/**
			 return max
			 */
			static inline double const & max() ;
			/**
			 compute absolute value
			 */
			static inline double abs(double const &);
	};


	/**
	  concrete fp traits class, spezialization for double,
	  rounding type 0, use down and up native
	 */
	template<>
	class
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
		fp_traits<double,native_switched> 
		: 
		public rounding_control<double,true>,
		public fp_traits_base<double>
	{
		protected:
			/**
			 current precision for output
			 */
			static int precision_val;
		public:
		fp_traits();
		
		/**
		 setup
		 **/
		static inline void setup();

		/**
		 reset
		 **/
		static inline void reset();

		/**
		 return precision
		 */
		static inline int const & precision()
		{
			return precision_val;
		}
		/**
		 set precision
		 */
		static inline int precision(int const & new_val)
		{
			int old_val = precision_val;
			precision_val = new_val;
			return old_val;
		}

		
		/**
		 binary operation plus with rounding upward
		 */
		template<bool r>
		static inline double upward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r>
		static inline double downward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r>
		static inline double tozero_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r>
		static inline double tonearest_plus(
			double const &,
			double const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r>
		static inline double upward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r>
		static inline double downward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r>
		static inline double tozero_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r>
		static inline double tonearest_minus(
			double const &,
			double const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r>
		static inline double upward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r>
		static inline double downward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r>
		static inline double tozero_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r>
		static inline double tonearest_multiplies(
			double const &,
			double const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r>
		static inline double upward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r>
		static inline double downward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r>
		static inline double tozero_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r>
		static inline double tonearest_divides(
			double const &,
			double const &);

		// template wrappers begin
		static inline double upward_plus(double const &a, double const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline double upward_minus(double const &a, double const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline double upward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline double upward_divides(double const &a, double const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline double downward_plus(double const &a, double const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline double downward_minus(double const &a, double const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline double downward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline double downward_divides(double const &a, double const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline double tozero_plus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline double tozero_minus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline double tozero_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline double tozero_divides(double const &a, double const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline double tonearest_plus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline double tonearest_minus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline double tonearest_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline double tonearest_divides(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end
	};
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif		
		fp_traits<double,native_directed> 
		: 
		public rounding_control<double,false>,
		public fp_traits_base<double>
	{
		protected:
			/**
			 current precision for output
			 */
			static int precision_val;
		public:
		/**
		 constructor, used for bootstrapping
		 not for use during normal operation
		 (though it would not destroy anything,
		 it would just be useless)
		 */
		fp_traits();

		/**
		 setup
		 **/
		static inline void setup();

		/**
		 reset
		 **/
		static inline void reset();

		/**
		 return precision
		 */
		static inline int const & precision()
		{
			return precision_val;
		}
		/**
		 set precision
		 */
		static inline int precision(int const & new_val)
		{
			int old_val = precision_val;
			precision_val = new_val;
			return old_val;
		}

		/**
		 binary operation plus with rounding upward
		 */
		template<bool r> static inline double upward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline double downward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline double tozero_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_plus(
			double const &,
			double const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline double upward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline double downward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline double tozero_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_minus(
			double const &,
			double const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline double upward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline double downward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline double tozero_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline double tonearest_multiplies(
			double const &,
			double const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline double upward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline double downward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline double tozero_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline double tonearest_divides(
			double const &,
			double const &);
		// template wrappers begin
		static inline double upward_plus(double const &a, double const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline double upward_minus(double const &a, double const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline double upward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline double upward_divides(double const &a, double const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline double downward_plus(double const &a, double const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline double downward_minus(double const &a, double const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline double downward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline double downward_divides(double const &a, double const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline double tozero_plus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline double tozero_minus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline double tozero_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline double tozero_divides(double const &a, double const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline double tonearest_plus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline double tonearest_minus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline double tonearest_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline double tonearest_divides(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end	
	};

	/**
	 concrete fp traits class, spezialization for double,
	 rounding type 1, multiplicative
	 */
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
	fp_traits<double,multiplicative> 
		: 
		public rounding_control_stub,
		public fp_traits_base<double>
	{
		protected:
			/**
			 current precision for output
			 */
			static int precision_val;
		public:
		/**
		 constructor, used for bootstrapping
		 not for use during normal operation
		 (though it would not destroy anything,
		 it would just be useless)
		 */
		fp_traits();

		/**
		 setup
		 **/
		static inline void setup();

		/**
		 reset
		 **/
		static inline void reset();

		/**
		 return precision
		 */
		static inline int const & precision()
		{
			return precision_val;
		}
		/**
		 set precision
		 */
		static inline int precision(int const & new_val)
		{
			int old_val = precision_val;
			precision_val = new_val;
			return old_val;
		}

		/**
		 binary operation plus with rounding upward
		 */
		template<bool r> static inline double upward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline double downward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline double tozero_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_plus(
			double const &,
			double const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline double upward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline double downward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline double tozero_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_minus(
			double const &,
			double const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline double upward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline double downward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline double tozero_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline double tonearest_multiplies(
			double const &,
			double const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline double upward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline double downward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline double tozero_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline double tonearest_divides(
			double const &,
			double const &);
		/**
		 fake pred by multiplication
		 */
		static inline double low ( double const & );
		/**
		 fake succ by multiplication
		 */
		static inline double high ( double const & );
		// template wrappers begin
		static inline double upward_plus(double const &a, double const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline double upward_minus(double const &a, double const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline double upward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline double upward_divides(double const &a, double const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline double downward_plus(double const &a, double const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline double downward_minus(double const &a, double const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline double downward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline double downward_divides(double const &a, double const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline double tozero_plus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline double tozero_minus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline double tozero_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline double tozero_divides(double const &a, double const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline double tonearest_plus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline double tonearest_minus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline double tonearest_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline double tonearest_divides(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end	
	};
	/**
	 concrete fp traits class, spezialization for double,
	 rounding type 2, no rounding at all
	 */
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
		fp_traits<double,no_rounding> 
		: 
		public rounding_control_stub,
		public fp_traits_base<double>
	{
		protected:
			/**
			 current precision for output
			 */
			static int precision_val;
		public:
		/**
		 constructor, used for bootstrapping
		 not for use during normal operation
		 (though it would not destroy anything,
		 it would just be useless)
		 */
		fp_traits();

		/**
		 setup
		 **/
		static inline void setup();

		/**
		 reset
		 **/
		static inline void reset();

		/**
		 return precision
		 */
		static inline int const & precision()
		{
			return precision_val;
		}
		/**
		 set precision
		 */
		static inline int precision(int const & new_val)
		{
			int old_val = precision_val;
			precision_val = new_val;
			return old_val;
		}

		/**
		 binary operation plus with rounding upward
		 */
		template<bool r> static inline double upward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline double downward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline double tozero_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_plus(
			double const &,
			double const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline double upward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline double downward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline double tozero_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_minus(
			double const &,
			double const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline double upward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline double downward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline double tozero_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline double tonearest_multiplies(
			double const &,
			double const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline double upward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline double downward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline double tozero_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline double tonearest_divides(
			double const &,
			double const &);
		// template wrappers begin
		static inline double upward_plus(double const &a, double const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline double upward_minus(double const &a, double const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline double upward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline double upward_divides(double const &a, double const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline double downward_plus(double const &a, double const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline double downward_minus(double const &a, double const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline double downward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline double downward_divides(double const &a, double const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline double tozero_plus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline double tozero_minus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline double tozero_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline double tozero_divides(double const &a, double const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline double tonearest_plus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline double tonearest_minus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline double tonearest_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline double tonearest_divides(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end	
	};

	/**
	 concrete fp traits class, spezialization for double,
	 pred - succ rounding emulation
	 */
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
	fp_traits<double,pred_succ_rounding> 
		: 
		public rounding_control_stub,
		public fp_traits_base<double>
	{
		protected:
			/**
			 current precision for output
			 */
			static int precision_val;
		public:
		/**
		 constructor, used for bootstrapping
		 not for use during normal operation
		 (though it would not destroy anything,
		 it would just be useless)
		 */
		fp_traits();

		/**
		 setup
		 **/
		static inline void setup();

		/**
		 reset
		 **/
		static inline void reset();

		/**
		 return precision
		 */
		static inline int const & precision()
		{
			return precision_val;
		}
		/**
		 set precision
		 */
		static inline int precision(int const & new_val)
		{
			int old_val = precision_val;
			precision_val = new_val;
			return old_val;
		}

		/**
		 binary operation plus with rounding upward
		 */
		template<bool r> static inline double upward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline double downward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline double tozero_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_plus(
			double const &,
			double const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline double upward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline double downward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline double tozero_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_minus(
			double const &,
			double const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline double upward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline double downward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline double tozero_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline double tonearest_multiplies(
			double const &,
			double const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline double upward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline double downward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline double tozero_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline double tonearest_divides(
			double const &,
			double const &);
		// template wrappers begin
		static inline double upward_plus(double const &a, double const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline double upward_minus(double const &a, double const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline double upward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline double upward_divides(double const &a, double const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline double downward_plus(double const &a, double const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline double downward_minus(double const &a, double const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline double downward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline double downward_divides(double const &a, double const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline double tozero_plus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline double tozero_minus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline double tozero_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline double tozero_divides(double const &a, double const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline double tonearest_plus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline double tonearest_minus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline double tonearest_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline double tonearest_divides(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end	
	};

	/**
	 concrete fp traits class, spezialization for double,
	 native onesided global
	 */
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
	fp_traits<double,native_onesided_global>
		: 
		public rounding_control<double,false>,
		public fp_traits_base<double>
	{
		protected:
			/**
			 current precision for output
			 */
			static int precision_val;
		public:
		/**
		 constructor, used for bootstrapping
		 not for use during normal operation
		 (though it would not destroy anything,
		 it would just be useless)
		 */
		fp_traits();

		/**
		 setup
		 **/
		static inline void setup();

		/**
		 reset
		 **/
		static inline void reset();

		/**
		 return precision
		 */
		static inline int const & precision()
		{
			return precision_val;
		}
		/**
		 set precision
		 */
		static inline int precision(int const & new_val)
		{
			int old_val = precision_val;
			precision_val = new_val;
			return old_val;
		}

		/**
		 binary operation plus with rounding upward
		 */
		template<bool r> static inline double upward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline double downward_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline double tozero_plus(
			double const &,
			double const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_plus(
			double const &,
			double const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline double upward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline double downward_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline double tozero_minus(
			double const &,
			double const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline double tonearest_minus(
			double const &,
			double const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline double upward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline double downward_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline double tozero_multiplies(
			double const &,
			double const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline double tonearest_multiplies(
			double const &,
			double const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline double upward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline double downward_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline double tozero_divides(
			double const &,
			double const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline double tonearest_divides(
			double const &,
			double const &);
		// template wrappers begin
		static inline double upward_plus(double const &a, double const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline double upward_minus(double const &a, double const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline double upward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline double upward_divides(double const &a, double const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline double downward_plus(double const &a, double const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline double downward_minus(double const &a, double const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline double downward_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline double downward_divides(double const &a, double const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline double tozero_plus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline double tozero_minus(double const &a, double const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline double tozero_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline double tozero_divides(double const &a, double const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline double tonearest_plus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline double tonearest_minus(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline double tonearest_multiplies(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline double tonearest_divides(double const &a, double const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end	
	};
}

#include <ieee/primitive.hpp>
#include <fp_traits/fp_traits_base_double.icc>

#if defined(HAVE_SSE)
#include <fp_traits/fp_traits_double_sse_native_switched.icc>
#include <fp_traits/fp_traits_double_sse_native_directed.icc>
#include <fp_traits/fp_traits_double_sse_native_onesided_global.icc>
#include <fp_traits/fp_traits_double_sse_pred_succ_rounding.icc>
#include <fp_traits/fp_traits_double_sse_multiplicative.icc>
#include <fp_traits/fp_traits_double_sse_no_rounding.icc>
#elif defined(HAVE_X87)
#include <fp_traits/fp_traits_double_x87_native_switched.icc>
#include <fp_traits/fp_traits_double_x87_native_directed.icc>
#include <fp_traits/fp_traits_double_x87_native_onesided_global.icc>
#include <fp_traits/fp_traits_double_x87_pred_succ_rounding.icc>
#include <fp_traits/fp_traits_double_x87_multiplicative.icc>
#include <fp_traits/fp_traits_double_x87_no_rounding.icc> 
#else
#include <fp_traits/fp_traits_double_generic_native_switched.icc>
#include <fp_traits/fp_traits_double_generic_native_directed.icc>
#include <fp_traits/fp_traits_double_generic_native_onesided_global.icc>
#include <fp_traits/fp_traits_double_generic_pred_succ_rounding.icc>
#include <fp_traits/fp_traits_double_generic_multiplicative.icc>
#include <fp_traits/fp_traits_double_generic_no_rounding.icc>
#endif

#endif
