#if ! defined(FP_TRAITS_X87_CONST_HPP)
#define FP_TRAITS_X87_CONST_HPP

#include <rounding_control/rounding_control_config.hpp>

#if  defined(HAVE_X87)
#include "sys/types.h"

#if ! defined(u_int32_t)
#if defined(__MINGW32__)
typedef unsigned short u_int16_t;
#endif
#endif


namespace filib {
  namespace x87 {
    enum rounddir {
      dir_nearest = 0,
      dir_down = 1,
      dir_up = 2,
      dir_trunc = 3
    };
    
    struct x87Constants {
	    static u_int16_t s_i387_DOUBLE_ROUND_NEAR;
	    static u_int16_t s_i387_DOUBLE_ROUND_DOWN;
	    static u_int16_t s_i387_DOUBLE_ROUND_UP;
	    static u_int16_t s_i387_DOUBLE_ROUND_TRUNC;
	    
	    static u_int16_t s_i387_FLOAT_ROUND_NEAR;
	    static u_int16_t s_i387_FLOAT_ROUND_DOWN;
	    static u_int16_t s_i387_FLOAT_ROUND_UP;
	    static u_int16_t s_i387_FLOAT_ROUND_TRUNC;

	    // float
	    static void x87floatsetrounding(rounddir dir);
	    // double
	    static void x87doublesetrounding(rounddir dir);
    };

    inline void x87floatroundnear() { x87Constants::x87floatsetrounding(dir_nearest); }
    inline void x87floatroundup() { x87Constants::x87floatsetrounding(dir_up); }
    inline void x87floatrounddown() { x87Constants::x87floatsetrounding(dir_down); }
    inline void x87floatroundtrunc() { x87Constants::x87floatsetrounding(dir_trunc); }

    inline float x87add(float a, float b, bool const reset) {
      float c;
      if ( reset )
        asm volatile("fadd %2,%1 ; fldcw %3; fstp %0" : "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
      else
        asm volatile("fadd %2,%1; fstp %0" : "=m" (c) : "t" (a), "u" (b) : "st");

      return c;
    }
    inline float x87sub(float a, float b, bool const reset) {
      float c;
      if ( reset )
        asm volatile("fsub %2,%1 ; fldcw %3; fstp %0" : "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
      else
        asm volatile("fsub %2,%1; fstp %0" : "=m" (c) : "t" (a), "u" (b) : "st");

      return c;
    }
    inline float x87mul(float a, float b, bool const reset) {
      float c;
      if ( reset )
        asm volatile("fmul %2,%1 ; fldcw %3; fstp %0" : "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
      else
        asm volatile("fmul %2,%1; fstp %0" : "=m" (c) : "t" (a), "u" (b) : "st");

      return c;
    }
    inline float x87div(float a, float b, bool const reset) {
      float c;
      if ( reset )
        asm volatile("fdiv %2,%1 ; fldcw %3; fstp %0" : "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
      else
        asm volatile("fdiv %2,%1; fstp %0" : "=m" (c) : "t" (a), "u" (b) : "st");

      return c;
    }

    inline float x87add(float a, float b, rounddir dir, bool const reset) {
      float c;
      if ( reset )
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_UP), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
        }
      else
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_UP) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC) : "st");
            break;
        }
    
      return c;
    }

    inline float x87sub(float a, float b, rounddir dir, bool const reset) {
      float c;
      if ( reset )
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_UP), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
        }
      else
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_UP) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC) : "st");
            break;
        }
    
      return c;
    }

    inline float x87mul(float a, float b, rounddir dir, bool const reset) {
      float c;
      if ( reset )
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_UP), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
        }
      else
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_UP) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC) : "st");
            break;
        }
    
      return c;
    }

    inline float x87div(float a, float b, rounddir dir, bool const reset) {
      float c;
      if ( reset )
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_UP), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstp %0 ; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
        }
      else
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_DOWN) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_UP) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstp %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_FLOAT_ROUND_TRUNC) : "st");
            break;
        }
    
      return c;
    }


    inline void x87doubleroundnear() { x87Constants::x87doublesetrounding(dir_nearest); }
    inline void x87doubleroundup() { x87Constants::x87doublesetrounding(dir_up); }
    inline void x87doublerounddown() { x87Constants::x87doublesetrounding(dir_down); }
    inline void x87doubleroundtrunc() { x87Constants::x87doublesetrounding(dir_trunc); }

    inline double x87add(double a, double b, bool const reset) {
      double c;
      if ( reset )
        asm volatile("fadd %2,%1; fstpl %0; fldcw %3" : "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
      else
        asm volatile("fadd %2,%1; fstpl %0" : "=m" (c) : "t" (a), "u" (b) : "st");

      return c;
    }
    inline double x87sub(double a, double b, bool const reset) {
      double c;
      if ( reset )
        asm volatile("fsub %2,%1; fstpl %0;  fldcw %3" : "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
      else
        asm volatile("fsub %2,%1; fstpl %0" : "=m" (c) : "t" (a), "u" (b) : "st");

      return c;
    }
    inline double x87mul(double a, double b, bool const reset) {
      double c;
      if ( reset )
        asm volatile("fmul %2,%1; fstpl %0;  fldcw %3" : "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
      else
        asm volatile("fmul %2,%1; fstpl %0" : "=m" (c) : "t" (a), "u" (b) : "st");

      return c;
    }
    inline double x87div(double a, double b, bool const reset) {
      double c;
      if ( reset )
        asm volatile("fdiv %2,%1; fstpl %0;  fldcw %3" : "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
      else
        asm volatile("fdiv %2,%1; fstpl %0" : "=m" (c) : "t" (a), "u" (b) : "st");

      return c;
    }

    inline double x87add(double a, double b, rounddir dir, bool const reset) {
      double c;
      if ( reset )
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_UP), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
        }
      else
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_UP) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fadd %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC) : "st");
            break;
        }
    
      return c;
    }

    inline double x87sub(double a, double b, rounddir dir, bool const reset) {
      double c;
      if ( reset )
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_UP), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
        }
      else
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_UP) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fsub %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC) : "st");
            break;
        }
    
      return c;
    }

    inline double x87mul(double a, double b, rounddir dir, bool const reset) {
      double c;
      if ( reset )
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_UP), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
        }
      else
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_UP) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fmul %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC) : "st");
            break;
        }
    
      return c;
    }

    inline double x87div(double a, double b, rounddir dir, bool const reset) {
      double c;
      if ( reset )
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_UP), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstpl %0; fldcw %4" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
        }
      else
        switch ( dir ) {
          case dir_nearest:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_NEAR) : "st");
            break;
          case dir_down:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_DOWN) : "st");
            break;
          case dir_up:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_UP) : "st");
            break;
          case dir_trunc:
	    asm volatile("fldcw %3 ; fdiv %2,%1; fstpl %0" :  "=m" (c) : "t" (a), "u" (b), "m" (x87Constants::s_i387_DOUBLE_ROUND_TRUNC) : "st");
            break;
        }
    
      return c;
    }

    
  }  
}
#endif
#endif
