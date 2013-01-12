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

/// @addtogroup auxil
/// @{

/// returns pseudo-random double number from [0,d)
inline double random(double d){
  return double (std::rand())*d/RAND_MAX;
}
/// returns pseudo-random integer number from [0,d)
inline int random(int d){
  return int (std::rand())*d/RAND_MAX;
}

/// initializes pseudo-random numbers generator
inline void randomStart(int n=0){
   if(!n) n=std::time(0);
   std::srand(n);
}

/// @}
