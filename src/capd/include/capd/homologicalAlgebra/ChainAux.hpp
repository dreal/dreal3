/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ChainAux.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_CHAINAUX_HPP_)
#define _CHAINAUX_HPP_
#include "capd/homologicalAlgebra/ChainAux.h"
/*
  For the moment we have here only the implementation of matrixColumnsToChains
*/

// -------------------------------------------------------------------------------------- //

// ********** matrixColumnsToChains ********** //
template<typename freeModuleType>
void matrixColumnsToChains(
  const freeModuleType& A_BaseModule,
  const typename freeModuleType::MatrixType& A_matrix,
  std::vector<ChainAux<freeModuleType> >& A_chains
){
  int m=A_matrix.numberOfRows();
  int n=A_matrix.numberOfColumns();
  A_chains.reserve(n);
  for(int j=0;j<n;++j){
    ChainAux<freeModuleType> c;
    c.m_pBaseModule=&A_BaseModule;
    for(int i=0;i<m;++i){
      typename freeModuleType::MatrixType::ScalarType zero(0);
      if( A_matrix[i][j] != zero ){
        c.m_chainCoef.insert(make_pair(i,A_matrix[i][j]));
      }
    }
    A_chains.push_back(c);
  }
}  // ********** matrixColumnsToChains ********** //
#endif //_CHAINAUX_HPP_

/// @}

