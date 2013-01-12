/////////////////////////////////////////////////////////////////////////////
/// @file NewtonResult.h
///
/// @author Tomasz Kapela
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_NEWTON_NEWTONRESULT_H_ 
#define _CAPD_NEWTON_NEWTONRESULT_H_ 

namespace capd{
namespace newton{

/// Define results returned by Interval Newton Method
enum NewtonResult {ResultUndefined = -2,  TooManyIterations = -1, NoZeroes = 0, ZeroExists = 1};

typedef  NewtonResult KrawczykResult;

inline std::string resultToText(NewtonResult code)
{

   switch(code){
        case ZeroExists: return "There exists exactly one zero of a given function in this set.";

        case NoZeroes:  return "There are no zeroes of a given function in this set.";

        case TooManyIterations: return "We cannot conclude. Maximal number of taking intersection was exceeded.";

        case ResultUndefined:  return "\n We cannot conclude. Maybe estimates are not good enough.";

        default: return " Unknown Newton Result code."; 
     }
}

}} // namespace capd::newton

#endif // _CAPD_NEWTON_NEWTONRESULT_H_ 
