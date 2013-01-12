
/////////////////////////////////////////////////////////////////////////////
/// @file IntRounding.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2007 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_ROUNDING_INTROUNDING_H_ 
#define _CAPD_ROUNDING_INTROUNDING_H_ 

namespace capd{
namespace rounding{
 
/// @addtogroup rounding
/// @{

//////////////////////////////////////////////////////////////////////////////
//   IntRounding
///
///  Definition of class that virtually switches rounding modes of integer numbers
///  because in this case no switching is needed (all operations are exact)
///
///   @author Tomasz Kapela   @date 11-01-2006
//////////////////////////////////////////////////////////////////////////////
class IntRounding{

public:
  IntRounding();            ///<  Call initialization of Floating Point Unit

  static void roundNearest(){  ///<  Sets rounding to nearest mode
  }   
  static void roundUp(){       ///<  Sets rounding up mode
  }
  static void roundDown(){     ///<  Sets rounding down mode
  }
  static void roundCut(){      ///<  Sets rounding towards zero mode
  }
};

/// @}
}} // namespace capd::rounding

#endif // _CAPD_ROUNDING_INTROUNDING_H_ 

