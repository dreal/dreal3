/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ChainAux.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_CHAINAUX_H_)
#define _CHAINAUX_H_

template<typename freeModuleType>
class ChainAux;

template<typename freeModuleType>
void matrixColumnsToChains(
  const freeModuleType& A_BaseModule,
  const typename freeModuleType::MatrixType& A_matrix,
  std::vector<ChainAux<freeModuleType> >& A_chains
);



// ********** class ChainAux ********** //
/*
  This class for the moment plays only secondary role:
  it is used for proper formatting of chains, stores as
  columns of a matrix (see matrixColumnsToChains above, with implementation in ChainAux.hpp

  Eventually the class template ChainT should take over, in particular because
  the main method of this class, matrixColumnsToChains is now implemented
  in QuotientModule as exportBaseChains MM, 30-08-2006
*/

template<typename freeModuleType>
class ChainAux{
public:
  typedef typename freeModuleType::MatrixType MatrixType;
  typedef typename freeModuleType::MatrixType::ScalarType ScalarType;
  typedef typename std::map<int,typename MatrixType::ScalarType>::const_iterator const_iterator;
  ChainAux():m_pBaseModule(0){}
  friend std::ostream& operator<<(std::ostream& out, const ChainAux& c){
    for(
      const_iterator it=c.m_chainCoef.begin();
      it!=c.m_chainCoef.end();
      ++it
    ){
      if(it->second != ScalarType(0)){
        out << " ";
        if(!(it->second < ScalarType(0))) out << "+";
        if(it->second != ScalarType(1)) out << it->second;
        out << (*c.m_pBaseModule)[it->first];
      }
    }
    return out;
  }
  friend void matrixColumnsToChains<>(
    const freeModuleType& A_BaseModule,
    const typename freeModuleType::MatrixType& A_matrix,
    std::vector<ChainAux<freeModuleType> >& A_chains
  );
private:
  const freeModuleType* m_pBaseModule;
  std::map<int,typename MatrixType::ScalarType> m_chainCoef;
};// ********** class ChainAux ********** //
#endif //_CHAINAUX_H_

/// @}

