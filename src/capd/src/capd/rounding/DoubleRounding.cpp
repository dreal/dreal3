// @addtogroup rounding
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file doubleRounding.cpp
///
/// @author CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/rounding/DoubleRounding.h"

namespace capd{
namespace rounding{

#if CAPD_CPU_ARCH==CAPD_CPU_ARCH_X86

#ifdef INTEL_IM_CLEAR
// With this option an exception is generated for an invalid fp operation
#define X86_DEFAULT_FPU_FLAGS 0x03fe
#else
// Default - disable all exceptions
#define X86_DEFAULT_FPU_FLAGS 0x03ff
#endif


static unsigned short ROUND_NEAREST_CW = X86_DEFAULT_FPU_FLAGS;
static unsigned short ROUND_DOWN_CW    = X86_DEFAULT_FPU_FLAGS | 0x0400;
static unsigned short ROUND_UP_CW      = X86_DEFAULT_FPU_FLAGS | 0x0800;
static unsigned short ROUND_CUT_CW     = X86_DEFAULT_FPU_FLAGS | 0x0c00;

/* Rounding functions for x86 processors. GCC uses different asm syntax */
#ifdef __GNUC__

void DoubleRounding::roundNearest(void)
{
    asm volatile ("fldcw %0" : : "m" (ROUND_NEAREST_CW) );
}

void DoubleRounding::roundUp(void)
{
    asm volatile ("fldcw %0" : : "m" (ROUND_UP_CW) );
}

void DoubleRounding::roundDown(void)
{
    asm volatile ("fldcw %0" : : "m" (ROUND_DOWN_CW) );
}

void DoubleRounding::roundCut(void)
{
    asm volatile ("fldcw %0" : : "m" (ROUND_CUT_CW) );
}

#else

void DoubleRounding::roundNearest(void)
{
    asm fldcw [ROUND_NEAREST_CW];
}

void DoubleRounding::roundUp(void)
{
    asm fldcw [ROUND_UP_CW];
}

void DoubleRounding::roundDown(void)
{
    asm fldcw [ROUND_DOWN_CW];
}

void DoubleRounding::roundCut(void)
{
    asm fldcw [ROUND_CUT_CW];
}

#endif

#elif CAPD_CPU_ARCH==CAPD_CPU_ARCH_AMD64

// Note: on Pentium 4 loading the MXCSR register is extermly slow if it
// clears any xE flag. So the round* functions sets all masked flags (as
// if these functions encounted all possible arithmetic problems)
#ifdef INTEL_IM_CLEAR
// With this option an exception is generated for an invalid fp operation
#define AMD64_DEFAULT_SSE_FLAGS 0x1f3e
#else
// Default - disable all exceptions
#define AMD64_DEFAULT_SSE_FLAGS 0x1fbf
#endif

static unsigned int ROUND_NEAREST_CW = AMD64_DEFAULT_SSE_FLAGS;
static unsigned int ROUND_DOWN_CW    = AMD64_DEFAULT_SSE_FLAGS | 0x2000;
static unsigned int ROUND_UP_CW      = AMD64_DEFAULT_SSE_FLAGS | 0x4000;
static unsigned int ROUND_CUT_CW     = AMD64_DEFAULT_SSE_FLAGS | 0x6000;

#ifndef __GNUC__
#error AMD64 rounding code only available in GNU assembler convention
#endif

void DoubleRounding::roundNearest(void)
{
    asm volatile ("ldmxcsr %0" : : "m" (ROUND_NEAREST_CW) );
}

void DoubleRounding::roundUp(void)
{
    asm volatile ("ldmxcsr %0" : : "m" (ROUND_UP_CW) );
}

void DoubleRounding::roundDown(void)
{
    asm volatile ("ldmxcsr %0" : : "m" (ROUND_DOWN_CW) );
}

void DoubleRounding::roundCut(void)
{
    asm volatile ("ldmxcsr %0" : : "m" (ROUND_CUT_CW) );
}


#elif CAPD_CPU_ARCH==CAPD_CPU_ARCH_SPARC

/* SPARC functions already defined as inline functions in rounding.h */

#elif CAPD_CPU_ARCH==CAPD_CPU_ARCH_POWERPC

// The following assembly code for PowerPC (Mac) provided by Zin Arai.
  
void DoubleRounding::roundNearest(void){
    asm volatile ("mtfsfi 7,0");
}

void DoubleRounding::roundDown(void){
    asm volatile ("mtfsfi 7,3");
}

void DoubleRounding::roundUp(void){
    asm volatile ("mtfsfi 7,2");
}

void DoubleRounding::roundCut(void){
    asm volatile ("mtfsfi 7,1");
}

#else
#error No rounding implementation for this architecture
#endif

void DoubleRounding::initFpUnit()
{
  #if CAPD_CPU_ARCH==CAPD_CPU_ARCH_X86
    // For some reason Win98 turns off some of the error handling of INTEL processors,
    // so we first turn on all numerical error handling
    #ifdef __GNUC__          // GCC asm syntax
       asm volatile (
          "fninit\n\t"
      );
    #else                    // normal asm syntax
       asm              fninit;
    #endif
  #endif

  //finally we turn on rounding up, if necessary
  #ifdef UP_ROUNDING
    roundUp();
  #else
    roundNearest();          // called to reset other FPU flags on x86/x64
  #endif

}

 
DoubleRounding::DoubleRounding()
{
   initFpUnit();
}
   
RoundingMode DoubleRounding::test()
{
  double a,b,nexta,preva,nextb,eps;
  RoundingMode result= RoundUnknown;

  nexta=a=1.5;
  do{ 
    preva=a;
    a=nexta;
    nexta=(a-1.0)/2+1.0;
  }while(a!=nexta);

  nextb=-1.5;
  do{
    b=nextb;
    nextb=(b+1.0)/2-1.0;
  }while(b!=nextb);

  eps=((2*(preva-1))/3+1);
  
  if(a == 1 && b == -1 && eps == 1)
  {
    result=RoundCut;
  }
  else if(a>1  && (preva-1)/3>0)
  {
    result=RoundUp;
  }
  else if(b<-1)
  {
    result=RoundDown;
  }
  else
  {
    result=RoundNearest;
  }
  
  return result;

}

bool DoubleRounding::isWorking()
{
    RoundingMode mode;

    roundUp();
    mode = test();
    if (mode != RoundUp)
    {
//        cerr << "Round up mode not working: " << mode;
        return false;
    }

    roundDown();
    mode = test();
    if (mode != RoundDown)
    {
//        cerr << "Round down mode not working: " << mode;
        return false;
    }

    roundCut();
    mode = test();
    if (mode != RoundCut)
    {
//        cerr << "Round cut mode not working: " << mode;
        return false;
    }

    roundNearest();
    mode = test();
    if (mode != RoundNearest)
    {
//        cerr << "Round nearest mode not working: " << mode;
        return false;
    }
    
    return true;
}

}} // namespace capd::rounding

capd::rounding::DoubleRounding initRounding;
