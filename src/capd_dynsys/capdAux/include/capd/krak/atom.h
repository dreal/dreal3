/////////////////////////////////////////////////////////////////////////////
/// @file atom.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_ATOM_H_ 
#define _CAPD_KRAK_ATOM_H_ 

#  include <iostream>
#  include <fstream>

#define NONE  -1
#define Atom   0
#define STRING 1
#define LINK   2
#define HLINK  3
#define LIST   4
#define RECORD 5
#define ITEM   6
#define VAR    7
#define FIELD  8
#define CONST_STRING 9

namespace capd{
namespace krak{
   class frstring;
   void errorExit(const char *,...);
}}

// class atom is the parent class for classes frstring, item, var, list and record

namespace capd{
namespace krak{

class atom {
public:
   int virtual who(void) = 0 ;
   virtual ~atom(){}
   virtual atom *copy(void) = 0 ;
   virtual capd::krak::frstring descriptor(void) = 0 ;
   virtual void put(std::ostream &s){}
   int virtual operator<=(atom &a2);
   int virtual operator>=(atom &a2);
   int virtual operator==(atom &a2);
};//end class atom
}} // the end of the namespace capd::krak

inline int capd::krak::atom::operator<=(capd::krak::atom &a2)
{
   capd::krak::errorExit("Do not call functions from class atom");
   return 1;
}

inline int capd::krak::atom::operator>=(capd::krak::atom &a2)
{
   capd::krak::errorExit("Do not call functions from class atom");
   return 1;
}

inline int capd::krak::atom::operator==(capd::krak::atom &a2)
{
   capd::krak::errorExit("Do not call functions from class atom");
   return 1;
}

#endif // _CAPD_KRAK_ATOM_H_ 
