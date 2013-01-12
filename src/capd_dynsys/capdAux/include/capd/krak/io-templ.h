/////////////////////////////////////////////////////////////////////////////
/// @file io-templ.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

class interval;

template <class streamlikeClass>
inline streamlikeClass &operator<<(streamlikeClass &s, interval &iv){
//  s << "[" << iv.left_b() << "," << iv.right_b() << "]";
//  return s;
};
