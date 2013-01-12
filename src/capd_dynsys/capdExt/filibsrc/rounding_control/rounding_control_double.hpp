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
#if ! defined(ROUNDING_CONTROL_DOUBLE)
#define ROUNDING_CONTROL_DOUBLE

/**
  namespace for fast interval library
 */
namespace filib
{
	/**
	 G++ doesn't seem to understand partial specialization...
	 */
	template <bool C>
	class
#if defined(_MSC_VER) && defined(FILIB_DLL)
	__declspec(dllexport)
#elif defined(_MSC_VER) && ! defined(FILIB_DLL)
	__declspec(dllimport)
#endif
	rounding_control<double,C>
	{
		public:
		/**
		 setup
		 */
		static inline void setup();
		/**
		 set rounding mode to towards minus infinity
		 */
		static inline void downward();
		/**
		 set rounding mode to towards positive infinity
		 */
		static inline void upward();
		/**
		 set rounding mode to truncate
		 */
		static inline void tozero();
		/**
		 set rounding mode to round to nearest
		 */
		static inline void tonearest();
		/**
		 reset rounding
		 */
		static inline void reset();
	};
}

// include platform specific rounding code

// use asm inline code for GNU-Assembler on SPARC
#if defined(__GNUC__) && defined(__sparc)
#include <rounding_control/rounding_control_double_asmsparc.icc>

// rounding conforming to C9X, should be available on recent systems
#elif defined(__STDC_IEC_559__)
#include <rounding_control/rounding_control_double_iso9x.icc>

// ms vc
#elif defined(_MSC_VER) && (defined(__i386__) || defined(WIN32))
#include <rounding_control/rounding_control_double_asmmsvci386.icc>

// non native rounding
#else
#include <rounding_control/rounding_control_double_void.icc>

#endif

#endif
