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
#if ! defined(FP_TRAITS)
#define FP_TRAITS

#include <cmath>
#include <functional>

#include <rounding_control/rounding_control.hpp>
#include <rounding_control/rounding_control_stub.hpp>

/**
  namespace for fast interval arithmetic
 */
namespace filib
{
	template<typename N>
	class
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
	fp_traits_base
	{
		public:
		/**
		 is N negative ?
		 */
		static inline bool sign(N const &) ;
		/**
		 is N an invalid number
		 */
		static inline bool IsNaN(N const &) ;
		/**
		 is N infinite
		 */
		static inline bool IsInf(N const &) ;
		/**
		 return positive infinity
		 */
		static inline N const & infinity() ;
		/**
		 return negative infinity
		 */
		static inline N const & ninfinity() ;
		/**
		 return quiet NaN
		 */
		static inline N const & quiet_NaN() ;
		/**
		 return value below pi
		 */
		static inline N const & l_pi() ;
		/**
		 return value above pi
		 */
		static inline N const & u_pi() ;
		/**
		 return precision
		 */
		static inline int const & precision();
		/**
		 set precision
		 */
		static inline int precision(int);
		/**
		 compute absolute value
		 */
		static inline N abs(N const &);
	};
	/**
	 rounding strategies we support
	 
	 - native_switched:		do switching as called from interval
	 - native_directed:		native_switched without reset
	 - multiplicative: 		multiplicate with pred/succ of 0/1
	 - no_rounding:    		don't set rounding at all
	 - pred_succ_rounding:          use pred and succ
	 */
	enum rounding_strategy
	{
		native_switched = 0,
		native_directed = 1,
		multiplicative = 2,
		no_rounding = 3,
		native_onesided_global = 5,
		pred_succ_rounding = 6
	};
	/**
	  fp traits class interface. methods of course cannot
	  be static and virtual at the same time, so the body
	  is just provided as an interface hint (!)
	  an actual implementation will need some additional
	  constants !
	 */
	template <typename N, rounding_strategy K = native_switched>
	class
#if defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && defined(FILIB_BUILD_DLL) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
	fp_traits
	{
		public:
		/**
		 is N negative ?
		 */
		static inline bool sign(N const &) ;
		/**
		 is N an invalid number
		 */
		static inline bool IsNaN(N const &) ;
		/**
		 is N infinite
		 */
		static inline bool IsInf(N const &) ;
		/**
		 return positive infinity
		 */
		static inline N const & infinity() ;
		/**
		 return negative infinity
		 */
		static inline N const & ninfinity() ;
		/**
		 return quiet NaN
		 */
		static inline N const & quiet_NaN() ;
		/**
		 return value below pi
		 */
		static inline N const & l_pi() ;
		/**
		 return value above pi
		 */
		static inline N const & u_pi() ;
		/**
		 return precision
		 */
		static inline int const & precision();
		/**
		 set precision
		 */
		static inline int precision(int);
		/**
		 compute absolute value
		 */
		static inline N abs(N const &);

		/**
		 binary operation plus with rounding upward
		 */
		template<bool r>
		static inline N upward_plus(
			N const &,
			N const &);
		/**
		 binary operation plus with rounding downward
		 */
		template<bool r>
		static inline N downward_plus(
			N const &,
			N const &);
		/**
		 binary operation plus with tozero 
		 */
		template<bool r>
		static inline N tozero_plus(
			N const &,
			N const &);
		/**
		 binary operation plus with rounding to nearest
		 */
		template<bool r>
		static inline N tonearest_plus(
			N const &,
			N const &);

		/**
		 binary operation minus with rounding upward
		 */
		template<bool r>
		static inline N upward_minus(
			N const &,
			N const &);
		/**
		 binary operation minus with rounding downward
		 */
		template<bool r>
		static inline N downward_minus(
			N const &,
			N const &);
		/**
		 binary operation minus with tozero 
		 */
		template<bool r>
		static inline N tozero_minus(
			N const &,
			N const &);
		/**
		 binary operation minus with rounding to nearest
		 */
		template<bool r>
		static inline N tonearest_minus(
			N const &,
			N const &);

		/**
		 binary operation multiplies with rounding upward
		 */
		template<bool r>
		static inline N upward_multiplies(
			N const &,
			N const &);
		/**
		 binary operation multiplies with rounding downward
		 */
		template<bool r>
		static inline N downward_multiplies(
			N const &,
			N const &);
		/**
		 binary operation multiplies with tozero 
		 */
		template<bool r>
		static inline N tozero_multiplies(
			N const &,
			N const &);
		/**
		 binary operation multiplies with rounding to nearest
		 */
		template<bool r>
		static inline N tonearest_multiplies(
			N const &,
			N const &);

		/**
		 binary operation divides with rounding upward
		 */
		template<bool r>
		static inline N upward_divides(
			N const &,
			N const &);
		/**
		 binary operation divides with rounding downward
		 */
		template<bool r>
		static inline N downward_divides(
			N const &,
			N const &);
		/**
		 binary operation divides with tozero 
		 */
		template<bool r>
		static inline N tozero_divides(
			N const &,
			N const &);
		/**
		 binary operation divides with rounding to nearest
		 */
		template<bool r>
		static inline N tonearest_divides(
			N const &,
			N const &);
	};
}

#if defined(HAVE_SSE)
#include "fp_traits_sse_const.hpp"
#elif defined(HAVE_X87)
#include "fp_traits_x87_const.hpp"
#endif

#if defined(__KCC)
#define TEMPLATE_EMPTY
#else
#define TEMPLATE_EMPTY
#endif

#include <fp_traits/fp_traits_double.hpp>
#include <fp_traits/fp_traits_float.hpp>

/* makros for simplification */
#define FILIB_UPWARD_PLUS(R,A,B,r)		R=fp_traits<N,K>::upward_plus(A,B,r)
#define FILIB_DOWNWARD_PLUS(R,A,B,r)		R=fp_traits<N,K>::downward_plus(A,B,r)
#define FILIB_UPWARD_MINUS(R,A,B,r)		R=fp_traits<N,K>::upward_minus(A,B,r)
#define FILIB_DOWNWARD_MINUS(R,A,B,r)		R=fp_traits<N,K>::downward_minus(A,B,r)
#define FILIB_UPWARD_MULTIPLIES(R,A,B,r)	R=fp_traits<N,K>::upward_multiplies(A,B,r)
#define FILIB_DOWNWARD_MULTIPLIES(R,A,B,r)	R=fp_traits<N,K>::downward_multiplies(A,B,r)
#define FILIB_UPWARD_DIVIDES(R,A,B,r)		R=fp_traits<N,K>::upward_divides(A,B,r)
#define FILIB_DOWNWARD_DIVIDES(R,A,B,r)		R=fp_traits<N,K>::downward_divides(A,B,r)
#define FILIB_RESET				fp_traits<N,K>::reset()

#define FILIB_ISNAN(A)				fp_traits<N,K>::IsNaN(A)
#define FILIB_ISINF(A)				fp_traits<N,K>::IsInf(A)
#define FILIB_ABS(A)				fp_traits<N,K>::abs(A)
#define FILIB_MAX				fp_traits<N,K>::max_val
#define FILIB_MIN				fp_traits<N,K>::min_val
#define FILIB_QUIET_NAN				fp_traits<N,K>::nan_val
#define FILIB_INFINITY				fp_traits<N,K>::inf_val
#define FILIB_NINFINITY				fp_traits<N,K>::ninf_val
#define FILIB_L_PI				fp_traits<N,K>::l_pi_val
#define FILIB_U_PI				fp_traits<N,K>::u_pi_val

#endif
