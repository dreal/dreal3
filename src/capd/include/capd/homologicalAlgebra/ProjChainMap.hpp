/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ProjChainMap.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2010 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_PROJCHAINMAP_H_)
#define _PROJCHAINMAP_H_

#include "capd/auxil/CRef.h"

template<typename P_DomChain, typename P_RngChain>
class ProjChainMap{
  public:

    typedef P_DomChain DomChainType;
    typedef P_RngChain RngChainType;
    typedef typename DomChainType::ScalarType ScalarType;
    typedef typename DomChainType::GeneratorCodeType DomGenType;
    typedef typename RngChainType::GeneratorCodeType RngGenType;

    typedef typename DomChainType::const_iterator const_iterator;
    typedef RngGenType (*ProjMapType)(DomGenType);

    ProjChainMap(const ProjMapType& A_projMap):projMap(A_projMap){
    }

    CRef<RngChainType> operator()(const DomChainType& A_domChain) const{
      CRef<RngChainType> rngChainCR=CRef<RngChainType>(new RngChainType());
      for(const_iterator it=A_domChain.begin();it!=A_domChain.end();++it){
        const DomGenType& arg=it->first;
        const ScalarType& val=it->second;
// -- MM  std::cout << "c[" << arg << "]=" << val << std::endl;
        const RngGenType argProj=projMap(arg);
        if(argProj.ownDim()==arg.ownDim() && val!=ScalarType(0)){
// -- MM  std::cout << "  c'[" << argProj << "]=" << rngChainCR()[argProj] << " Adding " << val << std::endl;
          rngChainCR()[argProj]+=val;
          if(rngChainCR()[argProj]==ScalarType(0)){
            rngChainCR().erase(argProj);
          }
        }else{
// -- MM  std::cout << "  different dimensions: argProj=" << argProj.ownDim() << " arg=" << arg.ownDim() << std::endl;
        }
      }
      return rngChainCR;
    }

  private:
    const ProjMapType& projMap;


};



#endif //_PROJCHAINMAP_H_
/// @}
