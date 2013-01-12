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
#if ! defined(FP_TRAITS_FLOAT)
#define FP_TRAITS_FLOAT

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
		fp_traits_base<float>
	{
		public:
			/**
			 minimum
			 */
			static float const min_val;
			/**
			 maximum
			 */
			static float const max_val;
			/**
			 not a number
			 */
			static float const nan_val;
			/**
			 (positive) infinity
			 */
			static float const inf_val;
			/**
			 negative infinity
			 */
			static float const ninf_val;
			/**
			 value under pi
			 */
			static float const l_pi_val;
			/**
			 value above pi
			 */
			static float const u_pi_val;

			/**
			 is float negative ?
			 */
			static inline bool sign(float const &) ;
			/**
			 is float an invalid number
			 */
			static inline bool IsNaN(float const &) ;
			/**
			 is float infinite
			 */
				static inline bool IsInf(float const &) ;
			/**
			 return positive infinity
			 */
			static inline float const & infinity() ;
			/**
			 return negative infinity
			 */
			static inline float const & ninfinity() ;
			/**
			 return quiet NaN
			 */
			static inline float const & quiet_NaN() ;
			/**
			 return value below pi
			 */
			static inline float const & l_pi() ;
			/**
			 return value above pi
			 */
			static inline float const & u_pi() ;
			/**
			 return min
			 */
			static inline float const & min() ;
			/**
			 return max
			 */
			static inline float const & max() ;
			/**
			 compute absolute value
			 */
			static inline float abs(float const &);
	};
	/**
	  concrete fp traits class, spezialization for float,
	  rounding type 0, use down and up native
	 */
	template<>
	class
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
		fp_traits<float,native_switched> 
		: 
		public rounding_control<float,true>,
		public fp_traits_base<float>
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
		template<bool r> static inline float upward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline float downward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline float tozero_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_plus(
			float const &,
			float const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline float upward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline float downward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline float tozero_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_minus(
			float const &,
			float const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline float upward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline float downward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline float tozero_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline float tonearest_multiplies(
			float const &,
			float const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline float upward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline float downward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline float tozero_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline float tonearest_divides(
			float const &,
			float const &);

		// template wrappers begin
		static inline float upward_plus(float const &a, float const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline float upward_minus(float const &a, float const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline float upward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline float upward_divides(float const &a, float const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline float downward_plus(float const &a, float const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline float downward_minus(float const &a, float const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline float downward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline float downward_divides(float const &a, float const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline float tozero_plus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline float tozero_minus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline float tozero_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline float tozero_divides(float const &a, float const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline float tonearest_plus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline float tonearest_minus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline float tonearest_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline float tonearest_divides(float const &a, float const & b, bool r) {
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
		fp_traits<float,native_directed> 
		: 
		public rounding_control<float,false>,
		public fp_traits_base<float>
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
		template<bool r> static inline float upward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline float downward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline float tozero_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_plus(
			float const &,
			float const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline float upward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline float downward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline float tozero_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_minus(
			float const &,
			float const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline float upward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline float downward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline float tozero_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline float tonearest_multiplies(
			float const &,
			float const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline float upward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline float downward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline float tozero_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline float tonearest_divides(
			float const &,
			float const &);
		// template wrappers begin
		static inline float upward_plus(float const &a, float const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline float upward_minus(float const &a, float const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline float upward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline float upward_divides(float const &a, float const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline float downward_plus(float const &a, float const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline float downward_minus(float const &a, float const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline float downward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline float downward_divides(float const &a, float const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline float tozero_plus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline float tozero_minus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline float tozero_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline float tozero_divides(float const &a, float const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline float tonearest_plus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline float tonearest_minus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline float tonearest_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline float tonearest_divides(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end
	};

	/**
	 concrete fp traits class, spezialization for float,
	 rounding type 1, multiplicative
	 */
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
		fp_traits<float,multiplicative> 
		: 
		public rounding_control_stub,
		public fp_traits_base<float>
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
		template<bool r> static inline float upward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline float downward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline float tozero_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_plus(
			float const &,
			float const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline float upward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline float downward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline float tozero_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_minus(
			float const &,
			float const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline float upward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline float downward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline float tozero_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline float tonearest_multiplies(
			float const &,
			float const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline float upward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline float downward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline float tozero_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline float tonearest_divides(
			float const &,
			float const &);
		/**
		 fake pred by multiplication
		 */
		static inline float low ( float const & );
		/**
		 fake succ by multiplication
		 */
		static inline float high ( float const & );
		// template wrappers begin
		static inline float upward_plus(float const &a, float const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline float upward_minus(float const &a, float const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline float upward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline float upward_divides(float const &a, float const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline float downward_plus(float const &a, float const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline float downward_minus(float const &a, float const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline float downward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline float downward_divides(float const &a, float const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline float tozero_plus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline float tozero_minus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline float tozero_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline float tozero_divides(float const &a, float const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline float tonearest_plus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline float tonearest_minus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline float tonearest_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline float tonearest_divides(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end
	};
	/**
	 concrete fp traits class, spezialization for float,
	 rounding type 2, no rounding at all
	 */
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif		
	fp_traits<float,no_rounding> 
		: 
		public rounding_control_stub,
		public fp_traits_base<float>
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
		template<bool r> static inline float upward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline float downward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline float tozero_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_plus(
			float const &,
			float const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline float upward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline float downward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline float tozero_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_minus(
			float const &,
			float const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline float upward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline float downward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline float tozero_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline float tonearest_multiplies(
			float const &,
			float const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline float upward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline float downward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline float tozero_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline float tonearest_divides(
			float const &,
			float const &);
		// template wrappers begin
		static inline float upward_plus(float const &a, float const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline float upward_minus(float const &a, float const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline float upward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline float upward_divides(float const &a, float const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline float downward_plus(float const &a, float const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline float downward_minus(float const &a, float const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline float downward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline float downward_divides(float const &a, float const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline float tozero_plus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline float tozero_minus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline float tozero_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline float tozero_divides(float const &a, float const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline float tonearest_plus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline float tonearest_minus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline float tonearest_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline float tonearest_divides(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end
	};

	/**
	 concrete fp traits class, spezialization for float,
	 native onesided global rounding
	 */
	template<>
	class 
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif		
	fp_traits<float,native_onesided_global>
		: 
		public rounding_control<float,false>,
		public fp_traits_base<float>
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
		
		/** setup */
		static void setup();
		/** reset */
		static void reset();

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
		template<bool r> static inline float upward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r> static inline float downward_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r> static inline float tozero_plus(
			float const &,
			float const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_plus(
			float const &,
			float const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r> static inline float upward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r> static inline float downward_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r> static inline float tozero_minus(
			float const &,
			float const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r> static inline float tonearest_minus(
			float const &,
			float const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r> static inline float upward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r> static inline float downward_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r> static inline float tozero_multiplies(
			float const &,
			float const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r> static inline float tonearest_multiplies(
			float const &,
			float const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r> static inline float upward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r> static inline float downward_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r> static inline float tozero_divides(
			float const &,
			float const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r> static inline float tonearest_divides(
			float const &,
			float const &);
		// template wrappers begin
		static inline float upward_plus(float const &a, float const & b, bool r) {
			if ( r ) return upward_plus<true>(a,b); else return upward_plus<false>(a,b);
		}
		static inline float upward_minus(float const &a, float const & b, bool r) {
			if ( r ) return upward_minus<true>(a,b); else return upward_minus<false>(a,b);
		}
		static inline float upward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return upward_multiplies<true>(a,b); else return upward_multiplies<false>(a,b);
		}
		static inline float upward_divides(float const &a, float const & b, bool r) {
			if ( r ) return upward_divides<true>(a,b); else return upward_divides<false>(a,b);
		}
		static inline float downward_plus(float const &a, float const & b, bool r) {
			if ( r ) return downward_plus<true>(a,b); else return downward_plus<false>(a,b);
		}
		static inline float downward_minus(float const &a, float const & b, bool r) {
			if ( r ) return downward_minus<true>(a,b); else return downward_minus<false>(a,b);
		}
		static inline float downward_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return downward_multiplies<true>(a,b); else return downward_multiplies<false>(a,b);
		}
		static inline float downward_divides(float const &a, float const & b, bool r) {
			if ( r ) return downward_divides<true>(a,b); else return downward_divides<false>(a,b);
		}
		static inline float tozero_plus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_plus<true>(a,b); else return tozero_plus<false>(a,b);
		}
		static inline float tozero_minus(float const &a, float const & b, bool r) {
			if ( r ) return tozero_minus<true>(a,b); else return tozero_minus<false>(a,b);
		}
		static inline float tozero_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tozero_multiplies<true>(a,b); else return tozero_multiplies<false>(a,b);
		}
		static inline float tozero_divides(float const &a, float const & b, bool r) {
			if ( r ) return tozero_divides<true>(a,b); else return tozero_divides<false>(a,b);
		}
		static inline float tonearest_plus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_plus<true>(a,b); else return tonearest_plus<false>(a,b);
		}
		static inline float tonearest_minus(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_minus<true>(a,b); else return tonearest_minus<false>(a,b);
		}
		static inline float tonearest_multiplies(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_multiplies<true>(a,b); else return tonearest_multiplies<false>(a,b);
		}
		static inline float tonearest_divides(float const &a, float const & b, bool r) {
			if ( r ) return tonearest_divides<true>(a,b); else return tonearest_divides<false>(a,b);
		}
		// template wrappers end
	};
}

#include <ieee/primitive.hpp>
#include <fp_traits/fp_traits_base_float.icc>

#if defined(HAVE_SSE)
#include <fp_traits/fp_traits_float_sse_native_switched.icc>
#include <fp_traits/fp_traits_float_sse_native_directed.icc>
#include <fp_traits/fp_traits_float_sse_native_onesided_global.icc>
#include <fp_traits/fp_traits_float_sse_multiplicative.icc>
#include <fp_traits/fp_traits_float_sse_no_rounding.icc>
#elif defined(HAVE_X87)
#include <fp_traits/fp_traits_float_x87_native_switched.icc>
#include <fp_traits/fp_traits_float_x87_native_directed.icc>
#include <fp_traits/fp_traits_float_x87_native_onesided_global.icc>
#include <fp_traits/fp_traits_float_x87_multiplicative.icc>
#include <fp_traits/fp_traits_float_x87_no_rounding.icc>
#else
#include <fp_traits/fp_traits_float_generic_native_switched.icc>
#include <fp_traits/fp_traits_float_generic_native_directed.icc>
#include <fp_traits/fp_traits_float_generic_native_onesided_global.icc>
#include <fp_traits/fp_traits_float_generic_multiplicative.icc>
#include <fp_traits/fp_traits_float_generic_no_rounding.icc>
#endif

#endif
