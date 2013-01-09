/// @addtogroup auxil
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file random.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <cstdlib>
#include <ctime>

inline double random(double d){
  return double (std::rand())*d/RAND_MAX;
}

inline int random(int d){
  return int (std::rand())*d/RAND_MAX;
}

inline void randomStart(int n=0){
   if(!n) n=std::time(0);
   std::srand(n);
}
