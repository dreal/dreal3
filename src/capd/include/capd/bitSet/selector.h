/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file selector.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_BITSET_SELECTOR_H_ 
#define _CAPD_BITSET_SELECTOR_H_ 
typedef bool (*selectorType)(const int*);

class HiperSurfSelector{
  int m_direction,m_frequency,m_value;
public:
  HiperSurfSelector(int A_direction,int A_frequency,int A_value=0):m_direction(A_direction),m_frequency(A_frequency),m_value(A_value){}
  bool operator()(const int* coord) const{
    return coord[m_direction] % m_frequency == m_value;
  }
};

#endif // _CAPD_BITSET_SELECTOR_H_ 

/// @}
