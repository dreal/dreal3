/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file IdChainMap.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2010 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*
   Method not tested yet. Intended for a replacement of inclusion homology
   based on ChainMapHomology.
*/

#if !defined(_IDCHAINMAP_H_)
#define _IDCHAINMAP_H_

#include "capd/auxil/CRef.h"

template<typename P_Gen, typename P_Scalar>
class IdChainMap{
  public:
    typedef P_Scalar ScalarType;
    typedef ChainT<std::map<P_Gen,ScalarType> > ChainType;

    CRef<ChainType> operator()(const ChainType& A_domChainCR){
      return A_domChainCR;
    }


};



#endif //_IDCHAINMAP_H_
/// @}
