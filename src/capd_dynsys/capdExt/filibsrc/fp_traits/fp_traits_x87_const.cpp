#include "fp_traits_x87_const.hpp"

#if defined(HAVE_X87)

namespace filib {
  namespace x87 {
    u_int16_t x87Constants::s_i387_DOUBLE_ROUND_NEAR  = 0x027F;
    u_int16_t x87Constants::s_i387_DOUBLE_ROUND_DOWN  = 0x067F;
    u_int16_t x87Constants::s_i387_DOUBLE_ROUND_UP    = 0x0A7F;
    u_int16_t x87Constants::s_i387_DOUBLE_ROUND_TRUNC = 0x0E7F;

    u_int16_t x87Constants::s_i387_FLOAT_ROUND_NEAR  = 0x007F;
    u_int16_t x87Constants::s_i387_FLOAT_ROUND_DOWN  = 0x047F;
    u_int16_t x87Constants::s_i387_FLOAT_ROUND_UP    = 0x087F;
    u_int16_t x87Constants::s_i387_FLOAT_ROUND_TRUNC = 0x0C7F;    

    void x87Constants::x87floatsetrounding(rounddir dir) {
    	switch ( dir ) {
    		case dir_nearest:
    			asm volatile("fldcw %0" : : "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR));
			break;
		case dir_up:
			asm volatile("fldcw %0" : : "m" (x87Constants::s_i387_FLOAT_ROUND_UP));
			break;
		case dir_down:
			asm volatile("fldcw %0" : : "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN));
			break;
		case dir_trunc:
			asm volatile("fldcw %0" : : "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC));
			break;
		}
	}

  void x87Constants::x87doublesetrounding(rounddir dir) {
  	switch ( dir ) {
  		case dir_nearest:
  			asm volatile("fldcw %0" : : "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
  			break;
		case dir_up:
			asm volatile("fldcw %0" : : "m" (x87Constants::s_i387_DOUBLE_ROUND_UP) : "st");
			break;
		case dir_down:
			asm volatile("fldcw %0" : : "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN) : "st");
			break;
		case dir_trunc:
			asm volatile("fldcw %0" : : "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC) : "st");
			break;
	}
  }

  }
}
#endif
