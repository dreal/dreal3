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
#if ! defined(_CAPD_BASICALG_IEEE_PRIMITIVE_)
#define _CAPD_BASICALG_IEEE_PRIMITIVE_

#include <sys/types.h>
#include <stdlib.h>  /* needed for strtod */
#include <iostream>
#include <stdexcept>
#include <string>
#include <exception>
#include <vector>

#define USE_PRED_SUCC_TABLES

namespace capd{
namespace basicalg{

    struct interval_io_exception : public std::exception
	{
		private:
		std::string desc;

		public:
		interval_io_exception(std::string const & rdesc) throw()
		: desc(rdesc) {}
		virtual ~interval_io_exception() throw() {};
		virtual char const * what() const throw()
		{ return desc.c_str(); }
	};

	typedef union 
	{
		double f;

		struct 
		{
			#if defined(__sparc)
				#if defined(BYTE_ORDER)
				#undef BYTE_ORDER
				#endif
				#if defined(LITTLE_ENDIAN)
				#undef LITTLE_ENDIAN
				#endif
				#if defined(BIG_ENDIAN)
				#undef BIG_ENDIAN
				#endif
				#define LITTLE_ENDIAN 1234
				#define BIG_ENDIAN 4321
				#define BYTE_ORDER BIG_ENDIAN
			#endif

			#if !defined(BYTE_ORDER) && defined(__i386__)
			#define BYTE_ORDER LITTLE_ENDIAN
			#endif

			#if !defined(BYTE_ORDER) && defined(WIN32)
			#define BYTE_ORDER LITTLE_ENDIAN
			#endif

			#if !defined(BYTE_ORDER)
			#error "Undefined byte order."
			#endif

			#if (BYTE_ORDER == LITTLE_ENDIAN)
				unsigned int mant1 :32;
				unsigned int mant0 :20;
				unsigned int expo  :11;
				unsigned int sign  : 1;
			#elif (BYTE_ORDER == BIG_ENDIAN)
				unsigned int sign  : 1;
				unsigned int expo  :11;
				unsigned int mant0 :20;
				unsigned int mant1 :32;
			#elif (BYTE_ORDER == PDP_ENDIAN)
				#error "Sorry, byte order for PDP is unimplemented."
			#else
				#error "Sorry, your machines byte order is unknown."
			#endif
		} ieee;
	} a_diee;

	typedef union 
	{
		float f;

		struct 
		{
			#if (BYTE_ORDER == LITTLE_ENDIAN)
				unsigned int mant  :23;
				unsigned int expo  : 8;
				unsigned int sign  : 1;
			#elif (BYTE_ORDER == BIG_ENDIAN)
				unsigned int sign  : 1;
				unsigned int expo  : 8;
				unsigned int mant  :23;
			#elif (BYTE_ORDER == PDP_ENDIAN)
				#error "Sorry, byte order for PDP is unimplemented."
			#else
				#error "Sorry, your machines byte order is unknown."
			#endif
		} ieee;
	} a_fiee;

	class
	Primitive
	{
		public:
		
		static inline double const & MIN()
		{
			return min;
		}
  
		static inline double const & MIN_NORM() 
		{
			return minNorm;
		}
  
		static inline double const & MAX()
		{
			return max;
		}

		static inline double const & POS_INFTY() 
		{
			return posInf;
		}
  
		static inline double const & NEG_INFTY() 
		{
			return negInf;
		}

		static inline double const & QUIET_NAN() 
		{
			return qNaN;
		}

		static void basicBitImage(double const & d, std::ostream &os);
		static void basicBitImage(float const & d, std::ostream &os);
		static void basicHexImage(double const & d, std::ostream &os);
		static void basicHexImage(float const & d, std::ostream &os);

		static inline bool isInfinite(double const & x) 
		{
			a_diee const * y = reinterpret_cast<a_diee const *>(&x);
			return 
				y->ieee.expo	== 0x7FF	&&
				y->ieee.mant0	== 0		&& 
				y->ieee.mant1	== 0;
		}
  
		static inline bool isNaN(double const & x) 
		{
			#if defined(__KCC)
				// workaround for optimization bug in KCC 3.4; 
				// x != x will be optimized away !
				a_diee const * y = reinterpret_cast<a_diee const *>(&x);
				return 
					y->ieee.expo == 0x7FF && 
					(
						y->ieee.mant0 != 0 ||
						y->ieee.mant1 != 0
					);
			#else
				return x != x;
			#endif
		}

		static inline bool isRegular(double const & x) 
		{
			return !(isInfinite(x) || isNaN(x));
		}
  
		static inline bool sign(double const & x) 
		{
			a_diee const * y = reinterpret_cast<a_diee const *>(&x);
			return y->ieee.sign;
		}
  
		static inline double abs(double const & x) 
		{
			a_diee y;
			y.f = x;
			y.ieee.sign = 0;
			return y.f;
		}

		static inline bool isdenorm(double const & x) 
		{
			a_diee y;
			y.f = x;
			return (y.ieee.expo == 0) && (y.ieee.mant0 || y.ieee.mant1); 
		}

		static inline bool isdenormorzero(double const & x) 
		{
			a_diee y;
			y.f = x;
			return (y.ieee.expo == 0);
		}

		static inline bool isdenormorzerof(float const & x) 
		{
			a_fiee y;
			y.f = x;
			return (y.ieee.expo == 0);
		}

		static inline double compose(
			unsigned int const & rsign,
			unsigned int const & rexpo,
			unsigned int const & rmantUpper,
			unsigned int const & rmantLower
		)
		{
			a_diee f;
			f.ieee.sign  = rsign;
			f.ieee.expo  = rexpo;
			f.ieee.mant0 = rmantUpper;
			f.ieee.mant1 = rmantLower;

			return f.f;
		}

		static inline float composef(
			unsigned int const & rsign,
			unsigned int const & rexpo,
			unsigned int const & rmant
		)
		{
			a_fiee f;
			f.ieee.sign  = rsign;
			f.ieee.expo  = rexpo;
			f.ieee.mant  = rmant;
			return f.f;
		}

		static inline void decompose(
			double const & rx,
			unsigned int & rsign,
			unsigned int & rexpo,
			unsigned int & rmantUpper,
			unsigned int & rmantLower
		)
		{
			a_diee const * f = reinterpret_cast<a_diee const *>(&rx);
			rsign      = f->ieee.sign;
			rexpo      = f->ieee.expo;
			rmantUpper = f->ieee.mant0;
			rmantLower = f->ieee.mant1;
		}

		static inline void decomposef(
			float const & rx,
			unsigned int & rsign,
			unsigned int & rexpo,
			unsigned int & rmant
		)
		{
			a_fiee const * f = reinterpret_cast<a_fiee const *>(&rx);
			rsign = f->ieee.sign;
			rexpo = f->ieee.expo;
			rmant = f->ieee.mant;
		}

		static inline double ulp(double const & x)
		{
			if (isInfinite(x))
			{
				return POS_INFTY();
			}
			else if (isNaN(x))
			{
				return x;
			}
			else
			{
				a_diee ulpx;
				ulpx.f = x;
				ulpx.ieee.sign = 0;
      
				/**
				 * x is zero or denormalized
				 **/
				if (ulpx.ieee.expo == 0)
				{
					ulpx.ieee.mant0 = 0;
					ulpx.ieee.mant1 = 1;
					return ulpx.f;
				}
				/**
				 * non-underflow case
				 **/
				else if (ulpx.ieee.expo > 52)
				{
					ulpx.ieee.expo -= 52;
					ulpx.ieee.mant0 = 0;
					ulpx.ieee.mant1 = 0;
					return ulpx.f;
				}
				/**
				 * underflow case
				 **/
				else
				{
					unsigned int n = 52-ulpx.ieee.expo;
					ulpx.ieee.expo = 0;
					if (n < 20) 
					{
						ulpx.ieee.mant0 = (0x80000 >> n);
						ulpx.ieee.mant1 = 0;
					}
					else
					{
						ulpx.ieee.mant0 = 0;
						ulpx.ieee.mant1 = (0x80000000 >> (n-20));
					}
					return ulpx.f;
				}
			}
		}

		static void print(double const & x, std::ostream &os);
		static void bitImage(double const & x, std::ostream &os);
  
		/**
		 * predecessor and successor of a number
		 **/

		/**
		 * modified version of pred from original fi_lib
		 **/
		static inline double basic_pred(double const & y) 
		{  
			a_diee su;
			su.f=y;
			
			/**
			 * y < 0.0
			 **/
			if (su.ieee.sign==1)
			{
				if (su.ieee.expo != 2047)
                               {
					if (su.ieee.mant1==0xffffffff)
					{ 
						su.ieee.mant1=0; 

						if (su.ieee.mant0==0xfffff)
						{ 
							su.ieee.mant0=0; 
							su.ieee.expo++;
						}
						else
						{ 
							su.ieee.mant0++;
						}
					}
					else
					{ 
						su.ieee.mant1++;
					}
                               } 
			}
			/**
			 * y >= 0.0
			 **/
			else
			{
				if (su.ieee.expo != 2047)
				{
					if (su.ieee.sign==0 && su.ieee.expo==0 && su.ieee.mant0==0 && su.ieee.mant1==0)
					{
						su.ieee.sign=1;
						su.ieee.mant1=1;
					} 
					else
					{
						if (su.ieee.mant1==0)
						{ 
							su.ieee.mant1=0xffffffff; 

							if (su.ieee.mant0==0)
							{
								su.ieee.mant0=0xfffff; 
								su.ieee.expo--;
							}
							else
							{ 
								su.ieee.mant0--;
							}
						}
						else
						{ 
							su.ieee.mant1--;
						}
					}
				}
				/**
				 * y == +inf
				 **/
				else if (su.ieee.mant0 == 0 && su.ieee.mant1 == 0)
				{
					su.ieee.expo = 2046;
					su.ieee.mant0 = 0xfffff;
					su.ieee.mant1 = 0xffffffff;
				}
			}

			return su.f;
		}
  
		/**
		 * modified version of succ from original fi_lib
		 **/
		static inline double basic_succ(double const & y)
		{
			a_diee su;
			su.f=y;
			
			/**
			 * y >= 0.0
			 **/
			if (su.ieee.sign==0)
			{
				if (su.ieee.expo!=2047)
				{
					if (su.ieee.mant1==0xffffffff)
					{ 
						su.ieee.mant1=0; 

						if (su.ieee.mant0==1048575)
						{ 
							su.ieee.mant0=0; 
							su.ieee.expo++;
						}
						else
						{ 
							su.ieee.mant0++;
						}
					}
					else
					{ 
						su.ieee.mant1++;
					}
				}
			}
			/**
			 * y < 0.0
			 **/
			else
			{
				if (su.ieee.expo!=2047)
				{
					if (su.ieee.sign==1 && su.ieee.expo==0 && su.ieee.mant0==0 && su.ieee.mant1==0) 
					{
						su.ieee.sign=0;
						su.ieee.mant1=1;
					}
					else
					{
						if (su.ieee.mant1==0)
						{ 
							su.ieee.mant1=0xffffffff; 

							if (su.ieee.mant0==0)
							{ 
								su.ieee.mant0=1048575; 
								su.ieee.expo--;
							}
							else
							{ 
								su.ieee.mant0--;
							}
						}
						else
						{ 
							su.ieee.mant1--;
						}
					}
				}
				/**
				 * y == -inf
				 **/
				else if (su.ieee.mant0 == 0 && su.ieee.mant1 == 0) 
				{
					su.ieee.expo = 2046;
					su.ieee.mant0 = 0xfffff;
					su.ieee.mant1 = 0xffffffff;
				}
			}

			return su.f;
		}
		#if defined(USE_PRED_SUCC_TABLES)
		static inline double pred(double const & x)
		{ 
			a_diee f;
			f.f = x;

			unsigned int index = f.ieee.expo;

			if (f.ieee.sign == 0) 
			{
				if (f.ieee.mant1 == 0 && f.ieee.mant0 == 0)
				{
					/**
					 * special case: positive infinity
					 **/
					if (f.ieee.expo == 2047)
						return MAX();
					/**
					 * special case 2: positive powers of 2
					 **/
					else if (f.ieee.expo != 0)
						index--;
				}
			}
			/**
			 * special case: -max
			 **/
			else if (
				f.ieee.expo == 0x7FE &&
				f.ieee.mant0 == 0xFFFFF &&
				f.ieee.mant1 == 0xFFFFFFFF)
				return NEG_INFTY();
    
			return x-psTable.ULP[index];
		}
		static inline double succ(double const & x)
		{ 
			a_diee f;
			f.f = x;

			unsigned int index = f.ieee.expo;

			if (f.ieee.sign == 1)
			{
				if (f.ieee.mant1 == 0 && f.ieee.mant0 == 0)
				{
					/**
					 * special case: negative infinity
					 **/
					if (f.ieee.expo == 2047)
						return -MAX();
					/**
					 * special case: positive powers of 2
					 **/
					else if (f.ieee.expo != 0)
						index--;
				}
			}
			/**
			 * special case: max
			 **/
			else if (
				f.ieee.expo == 0x7FE &&
				f.ieee.mant0 == 0xFFFFF &&
				f.ieee.mant1 == 0xFFFFFFFF)
				return POS_INFTY();

			return x+psTable.ULP[index];
		}
		#else /** ! USE_PRED_SUCC_TABLES **/
		static inline double pred(double const & x) 
		{
			return basic_pred(x);
		}

		static inline double succ(double const & x) 
		{
			return basic_succ(x);
		}
		#endif /** USE_PRED_SUCC_TABLES **/
  
		private:

		static double min;
		static double minNorm;
		static double max;
		static double posInf;
		static double negInf;
		static double qNaN;

		static double computeMin();
		static double computeMinNorm();
		static double computeMax();
		static double computePosInf();
		static double computeNegInf();
		static double computeQNaN();

		#if defined(USE_PRED_SUCC_TABLES)
		/**
		 * for table version of pred and succ
		 **/
		class PredSuccTable 
		{
			public:
				PredSuccTable();
				~PredSuccTable();

				double *ULP;
		};
  
		static PredSuccTable psTable;
		#endif

		public:

		/**
		 * values used for multiplicative rounding
		 **/
		static double const zero_pred;
		static double const zero_succ;
		static double const one_pred;
		static double const one_succ;

		static float const zero_fpred;
		static float const zero_fsucc;
		static float const one_fpred;
		static float const one_fsucc;
	};

	void readBitSet(std::istream & in, unsigned int n0, unsigned char * a) throw(interval_io_exception);

	void readHexSet(std::istream & in, unsigned int n0, unsigned char * a) throw(interval_io_exception);

	void readChar(std::istream& in, char c0) throw(interval_io_exception);

	template <typename N>
	N constructFromBitSet(std::istream & in) throw(interval_io_exception)
	{
		throw interval_io_exception("constructFromBitSet() called for unsupported type");
	}
	template <typename N>
	N constructFromBitSet(std::string & in) throw(interval_io_exception)
	{
		throw interval_io_exception("constructFromBitSet() called for unsupported type");
	}
	template <typename N>
	N constructFromBitSet(char const * in) throw(interval_io_exception)
	{
		throw interval_io_exception("constructFromBitSet() called for unsupported type");
	}

	template <typename N>
	N constructFromHexSet(std::istream & in) throw(interval_io_exception)
	{
		throw interval_io_exception("constructFromHexSet() called for unsupported type");
	}
	template <typename N>
	N constructFromHexSet(std::string & in) throw(interval_io_exception)
	{
		throw interval_io_exception("constructFromHexSet() called for unsupported type");
	}
	template <typename N>
	N constructFromHexSet(char const * in) throw(interval_io_exception)
	{
		throw interval_io_exception("constructFromHexSet() called for unsupported type");
	}

	template<typename WS>
	void eatWS(std::istream & in)
	{
		char c = in.get();

		while ( in.good()  && WS::isSpace(c) )
			c = in.get();

		in.putback(c);
	}

	template<typename T>
	struct 	whitespace
	{
		static int isSpace(int);
	};

	template <>
	double constructFromBitSet<double>(std::istream & in) throw(interval_io_exception);

	template <>
	float constructFromBitSet<float>(std::istream & in) throw(interval_io_exception);

	template <>
	float constructFromBitSet<float>(std::string & in) throw(interval_io_exception);

	template <>
	double constructFromBitSet<double>(std::string & in) throw(interval_io_exception);

	template <>
	float constructFromBitSet<float>(char const * in) throw(interval_io_exception);

	template <>
	double constructFromBitSet<double>(char const * in) throw(interval_io_exception);

	template <>
	double constructFromHexSet<double>(std::istream & in) throw(interval_io_exception);
	template <>
	float constructFromHexSet<float>(std::istream & in) throw(interval_io_exception);
	template <>
	float constructFromHexSet<float>(std::string & in) throw(interval_io_exception);
	template <>
	double constructFromHexSet<double>(std::string & in) throw(interval_io_exception);
	template <>
	float constructFromHexSet<float>(char const * in) throw(interval_io_exception);
	template <>
	double constructFromHexSet<double>(char const * in) throw(interval_io_exception);

	template<>
	int whitespace<char>::isSpace(int arg);

	template <typename N, bool upDo>
	N inferFromString(std::string const &) throw(interval_io_exception){
		throw interval_io_exception("inferFromString() called for unsupported type");
	}

	template <>
	double inferFromString<double,false>(std::string const & )
	throw(interval_io_exception);

	template <>
	double inferFromString<double,true>(std::string const & )
	throw(interval_io_exception);

	template <>
	float inferFromString<float,false>(std::string const & )
	throw(interval_io_exception);

	template <>
	float inferFromString<float,true>(std::string const & )
	throw(interval_io_exception);

}} // namespace capd::basicalg

#endif // _CAPD_BASICALG_IEEE_PRIMITIVE_
