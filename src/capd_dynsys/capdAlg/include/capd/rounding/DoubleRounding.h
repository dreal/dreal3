
/////////////////////////////////////////////////////////////////////////////
/// @file DoubleRounding.h
///
/// @author CAPD group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_ROUNDING_DOUBLEROUNDING_H_ 
#define _CAPD_ROUNDING_DOUBLEROUNDING_H_ 

// This allows automatic detection of operating system and compiler
#include "capd/settings/archSetting.h"
//#include "capd/operatingSystemSetting.h"
//#include "capd/compilerSetting.h"

namespace capd{
namespace rounding{
/// @addtogroup rounding
/// @{

///  Rounding modes
enum RoundingMode { RoundUnknown= -1, RoundNearest, RoundDown, RoundUp,  RoundCut };
 
//////////////////////////////////////////////////////////////////////////////
//   DoubleRounding
///
///  Definition of class that switches rounding modes of double numbers
///
///   @author Tomasz Kapela   @date 11-01-2006
//////////////////////////////////////////////////////////////////////////////
class DoubleRounding{

    void initFpUnit();           ///<  Initialize Floating Point Unit

   public:
    DoubleRounding();            ///<  Call initialization of Floating Point Unit

    static void roundNearest();  ///<  Sets rounding to nearest mode
    
    static void roundUp();       ///<  Sets rounding up mode
    
    static void roundDown();     ///<  Sets rounding down mode
    
    static void roundCut();      ///<  Sets rounding towards zero mode

    static RoundingMode test();  ///<  Returns the actual rounding mode
    
    static bool isWorking();  ///<  Tests that all rounding modes works correctly. Returns false is they don't
};

#if CAPD_CPU_ARCH==CAPD_CPU_ARCH_SPARC
/* on SPARC rounding_* are inline wrappers around standard functions
 * on other architectures the functions are implemented in asm and shouldn't
 * be inline for the compiler not to reorder the instructions */

#include <ieeefp.h>

inline void DoubleRounding::roundNearest(){
  fpsetround(FP_RN);
}
inline void DoubleRounding::roundUp(){
  fpsetround(FP_RP);
}
inline void DoubleRounding::roundDown(){
  fpsetround(FP_RM);
}
inline void DoubleRounding::roundCut(){
  fpsetround(FP_RZ);
}

#endif

/// @}
}} // namespace capd::rounding

extern capd::rounding::DoubleRounding initRounding;

#endif // _CAPD_ROUNDING_DOUBLEROUNDING_H_ 

