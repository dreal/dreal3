/// @addtogroup 2
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file SetPairT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_SETPAIRT_H)
#define _SETPAIRT_H

#include "capd/auxil/CRef.h"
//#include "homologicalAlgebra/CrbInclHomology.hpp"

template<typename P_Set>
class SetPairT : public std::pair< CRef<P_Set>,CRef<P_Set> >{
  public:
  typedef P_Set SetType;
  SetPairT(CRef<SetType> A_subSetCR,CRef<SetType> A_supSetCR): std::pair< CRef<SetType>,CRef<SetType> >(A_subSetCR,A_supSetCR){}
  int cardinality(){
    return (this->second)().cardinality();
  }
  int embDim(){
    return (this->second)().embDim();
  }
  int getUnpaddedWidth(int j){
    return (this->second)().getUnpaddedWidth(j);
  }
};
#endif //_SETPAIRT_H

/// @}
