#include <fp_traits/fp_traits_sse_const.hpp>
#include <sys/types.h>

#if defined(HAVE_SSE)

namespace filib {
	namespace sse {
		u_int32_t sseConstants::mxcsr_down  = 0x00003f80;
		u_int32_t sseConstants::mxcsr_near  = 0x00001f80;
		u_int32_t sseConstants::mxcsr_up    = 0x00005f80;
		u_int32_t sseConstants::mxcsr_trunc = 0x00007f80;

		void sseConstants::ssesetrounding(rounddir dir) {
			switch ( dir ) {
				case dir_nearest:
					asm volatile ("ldmxcsr %0\n" : : "m" (sseConstants::mxcsr_near) );
					break;
				case dir_down:
					asm volatile ("ldmxcsr %0\n" : : "m" (sseConstants::mxcsr_down) );
					break;
				case dir_up:
					asm volatile ("ldmxcsr %0\n" : : "m" (sseConstants::mxcsr_up) );
					break;
				case dir_trunc:
					asm volatile ("ldmxcsr %0\n" : : "m" (sseConstants::mxcsr_trunc) );
					break;
			}
		}

	}
}
#endif
