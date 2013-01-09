/////////////////////////////////////////////////////////////////////////////
/// @addtogroup Interval
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file mpRounding.h
///
/// Functions that change rounding modes and precisions 
/// of Multi Precision Interval Arithmetic
///
/// @author Tomasz Kapela   @date 29-08-2006
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2006 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/multiPrec/MpSetting.h"
#ifdef __HAVE_MPFR__

#ifndef _CAPD_MULTIPREC_MPROUNDING_H_ 
#define _CAPD_MULTIPREC_MPROUNDING_H_ 

#include "capd/multiPrec/MpfrClass.h"
#ifdef USE_OLD_MPFRCLASS
namespace capd{
namespace multiPrec{
   
/////////////////////////////////////////////////////////////////////////////
// roundUp
///
///  sets rounding up mode 
/////////////////////////////////////////////////////////////////////////////
inline void roundUp()
{
  MpfrClass::setDefaultRndMode( MpfrClass::RoundUp);
}

/////////////////////////////////////////////////////////////////////////////
// roundDown
///
///  sets rounding down mode 
/////////////////////////////////////////////////////////////////////////////
inline void roundDown()
{
  MpfrClass::setDefaultRndMode( MpfrClass::RoundDown);
}

/////////////////////////////////////////////////////////////////////////////
// roundNearest
///
///  sets rounding to the nearest mode 
/////////////////////////////////////////////////////////////////////////////
inline void roundNearest()
{
  MpfrClass::setDefaultRndMode( MpfrClass::RoundNearest);
}

/////////////////////////////////////////////////////////////////////////////
// setPrecision
///
///  sets default precision for all multi precision operations
///
///  @param[in]  newprec   new precision (number of mantisa bits)
///
/////////////////////////////////////////////////////////////////////////////
inline void setPrecision(MpfrClass::PrecisionType newprec)
{
   MpfrClass::setDefaultPrecision(newprec);  
}

/////////////////////////////////////////////////////////////////////////////
// getPrecision
///
///  @returns default precision for all multi precision operations
///
/////////////////////////////////////////////////////////////////////////////
inline MpfrClass::PrecisionType getPrecision()
{
   return MpfrClass::getDefaultPrecision();  
}

}}  // end of namespace capd::multiPrec

#endif

#endif // _CAPD_MULTIPREC_MPROUNDING_H_ 

#endif  // __HAVE_MPFR__

/// @}
