#if ! defined(FP_TRAITS_SSE_CONST_HPP)
#define FP_TRAITS_SSE_CONST_HPP

#include <rounding_control/rounding_control_config.hpp>

#if  defined(HAVE_SSE)
#include "sys/types.h"

#if ! defined(u_int32_t)
#if defined(__MINGW32__)
typedef unsigned int u_int32_t;
#endif
#endif

namespace filib {
	namespace sse {
		enum rounddir {
			dir_nearest = 0,
			dir_down = 1,
			dir_up = 2,
			dir_trunc = 3
		};
		
		struct sseConstants {
			static u_int32_t mxcsr_down;
			static u_int32_t mxcsr_near;
			static u_int32_t mxcsr_up;
			static u_int32_t mxcsr_trunc;

			static void ssesetrounding(rounddir dir);
		};


		inline void sseroundnear() { sseConstants::ssesetrounding(dir_nearest); }
		inline void sserounddown() { sseConstants::ssesetrounding(dir_down); }
		inline void sseroundup() { sseConstants::ssesetrounding(dir_up); }
		inline void sseroundtrunc() { sseConstants::ssesetrounding(dir_trunc); }

		inline double sseadd(double a, double b, bool const reset) {
			if ( ! reset )
				asm volatile ("addsd %1, %0\n" : "+x" (a) : "x" (b) );
			else
				asm volatile ("addsd %1, %0\n" "ldmxcsr %2\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
			return a;
		}
		inline double ssesub(double a, double b, bool const reset) {
			if ( ! reset )
				asm volatile ("subsd %1, %0\n" : "+x" (a) : "x" (b) );
			else
				asm volatile ("subsd %1, %0\n" "ldmxcsr %2\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
			return a;
		}
		inline double ssemul(double a, double b, bool const reset) {
			if ( ! reset )
				asm volatile ("mulsd %1, %0\n" : "+x" (a) : "x" (b) );
			else
				asm volatile ("mulsd %1, %0\n" "ldmxcsr %2\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
			return a;
		}
		inline double ssediv(double a, double b, bool const reset) {
			if ( ! reset )
				asm volatile ("divsd %1, %0\n" : "+x" (a) : "x" (b) );
			else
				asm volatile ("divsd %1, %0\n" "ldmxcsr %2\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
			return a;
		}

		inline double sseadd(double a, double b, rounddir dir, bool const reset) {
			if ( ! reset ) {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "addsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "addsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "addsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "addsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc) );
						break;
				}
			}
			else {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "addsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "addsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "addsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "addsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc), "m" (sseConstants::mxcsr_near) );
						break;
				}
			}
			return a;
		}

		inline double ssesub(double a, double b, rounddir dir, bool const reset) {
			if ( ! reset ) {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "subsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "subsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "subsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "subsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc) );
						break;
				}
			}
			else {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "subsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "subsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "subsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "subsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc), "m" (sseConstants::mxcsr_near) );
						break;
				}
			}
			return a;
		}

		inline double ssemul(double a, double b, rounddir dir, bool const reset) {
			if ( ! reset ) {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "mulsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "mulsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "mulsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "mulsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc) );
						break;
				}
			}
			else {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "mulsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "mulsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "mulsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "mulsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc), "m" (sseConstants::mxcsr_near) );
						break;
				}
			}
			return a;
		}

		inline double ssediv(double a, double b, rounddir dir, bool const reset) {
			if ( ! reset ) {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "divsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "divsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "divsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "divsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc) );
						break;
				}
			}
			else {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "divsd %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "divsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "divsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "divsd %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc), "m" (sseConstants::mxcsr_near) );
						break;
				}
			}
			return a;
		}

		inline float sseadd(float a, float b, bool const reset) {
			if ( ! reset )
				asm volatile ("addss %1, %0\n" : "+x" (a) : "x" (b) );
			else
				asm volatile ("addss %1, %0\n" "ldmxcsr %2\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
			return a;
		}
		inline float ssesub(float a, float b, bool const reset) {
			if ( ! reset )
				asm volatile ("subss %1, %0\n" : "+x" (a) : "x" (b) );
			else
				asm volatile ("subss %1, %0\n" "ldmxcsr %2\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
			return a;
		}
		inline float ssemul(float a, float b, bool const reset) {
			if ( ! reset )
				asm volatile ("mulss %1, %0\n" : "+x" (a) : "x" (b) );
			else
				asm volatile ("mulss %1, %0\n" "ldmxcsr %2\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
			return a;
		}
		inline float ssediv(float a, float b, bool const reset) {
			if ( ! reset )
				asm volatile ("divss %1, %0\n" : "+x" (a) : "x" (b) );
			else
				asm volatile ("divss %1, %0\n" "ldmxcsr %2\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
			return a;
		}

		inline float sseadd(float a, float b, rounddir dir, bool const reset) {
			if ( ! reset ) {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "addss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "addss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "addss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "addss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc) );
						break;
				}
			}
			else {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "addss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "addss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "addss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "addss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc), "m" (sseConstants::mxcsr_near) );
						break;
				}
			}
			return a;
		}

		inline float ssesub(float a, float b, rounddir dir, bool const reset) {
			if ( ! reset ) {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "subss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "subss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "subss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "subss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc) );
						break;
				}
			}
			else {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "subss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "subss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "subss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "subss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc), "m" (sseConstants::mxcsr_near) );
						break;
				}
			}
			return a;
		}

		inline float ssemul(float a, float b, rounddir dir, bool const reset) {
			if ( ! reset ) {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "mulss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "mulss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "mulss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "mulss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc) );
						break;
				}
			}
			else {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "mulss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "mulss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "mulss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "mulss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc), "m" (sseConstants::mxcsr_near) );
						break;
				}
			}
			return a;
		}

		inline float ssediv(float a, float b, rounddir dir, bool const reset) {
			if ( ! reset ) {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "divss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "divss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "divss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "divss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc) );
						break;
				}
			}
			else {
				switch ( dir ) {
					case dir_nearest:
						asm volatile ("ldmxcsr %2\n" "divss %1, %0\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_down:
						asm volatile ("ldmxcsr %2\n" "divss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_down), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_up:
						asm volatile ("ldmxcsr %2\n" "divss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_up), "m" (sseConstants::mxcsr_near) );
						break;
					case dir_trunc:
						asm volatile ("ldmxcsr %2\n" "divss %1, %0\n" "ldmxcsr %3\n" : "+x" (a) : "x" (b), "m" (sseConstants::mxcsr_trunc), "m" (sseConstants::mxcsr_near) );
						break;
				}
			}
			return a;
		}

		
	}
}
#endif

#endif
