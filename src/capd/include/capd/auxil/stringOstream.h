/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file stringOstream.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <sstream>

#if !defined(_STRINGOSTREAM_H_)
#define _STRINGOSTREAM_H_
template<typename T>
std::string& operator<<(std::string& s,const T& t){
  std::ostringstream is;
  is << t;
  s+=is.str();
  return s;
}
#endif //_STRINGOSTREAM_H_

/// @}
