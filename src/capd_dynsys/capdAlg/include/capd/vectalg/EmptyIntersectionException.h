/////////////////////////////////////////////////////////////////////////////
/// @file Vector.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.
#ifndef _CAPD_VECTALG_EMPTYINTERSECTIONEXCEPTION_H_
#define _CAPD_VECTALG_EMPTYINTERSECTIONEXCEPTION_H_

#include <stdexcept>

/// @addtogroup vectalg
/// @{

class EmptyIntersectionException : public std::runtime_error{
public:
  EmptyIntersectionException(const char * msg):std::runtime_error(msg){
  }
};

/// @}

#endif /* _CAPD_VECTALG_EMPTYINTERSECTIONEXCEPTION_H_ */
