/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file powerTwoCeiling.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_POWERTWOCEILING_H_)
#define _POWERTWOCEILING_H_
inline int powerTwoCeiling(int n){
  int k=1;
  while(k<n) k=k << 1;
  return k;
}

inline unsigned int baseTwoLog(unsigned long int n){
  int k=0;
  while(n>1){
    n=n >> 1;
    ++k;
  }
  return k;
}
#endif//_POWERTWOCEILING_H_

/// @}

