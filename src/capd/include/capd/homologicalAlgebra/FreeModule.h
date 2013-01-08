/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FreeModule.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_FREEMODULE_H_)
#define _FREEMODULE_H_

// ********** class FreeModule ********** //
/*
   This class serves as a container for a finitely generated free module.

   To save the memory generators are automatically indexed
   and in vector/matrix computations indexes replace actual generators.
   However, when necessary, for instance on output, the actual generators
   may be used again.

   To achieve this,  the generators of the module are stored in the map m_generatorIndex
   whose values serve as integer indexes of generators.
   To facilitate the access to the generator through its index,
   the vector element m_generatorPtrVect[i] stores a pointer
   to the generator of index i in the map m_generatorIndex

   In this way each generator is stored only once.

   The class has no methods changing its private members, once constructed, to guarantee
   that the pointers have proper values.
*/
#undef FreeModule

#include <map>

template<typename generatorType,typename matrixType>
class FreeModule{
public:
  typedef matrixType MatrixType;
  typedef typename MatrixType::ColumnVectorType ColumnVectorType;
  typedef typename MatrixType::ScalarType ScalarType;
  typedef int IntType;
  typedef generatorType GeneratorType;
  typedef typename std::map<generatorType,int>::iterator iterator;
  typedef typename std::map<generatorType,int>::const_iterator const_iterator;

  // --------------------------------------------------------------- //
  // default constructor generates a module with no generators (zero module)
  FreeModule():m_numberOfGenerators(0){}

  // --------------------------------------------------------------- //
  // This constructor takes a map A_generatorIndex of pairs (generatorType,int) as argument.
  // The int values in the map are irrelevant, may be all zero.
  // The map on input is swapped with the internal map, as a consequence the input is destroyed.
  // The resulting free module has as generators the keys of the map.
  // The constructor assigns indexes to the generators, stored as the values of the map m_generatorIndex.
  // The vector m_generatorPtrVect is assigned pointers to generators in the map m_generatorIndex
  FreeModule(std::map<generatorType,IntType>& A_generatorIndex){
    std::swap(m_generatorIndex,A_generatorIndex);
    m_numberOfGenerators=m_generatorIndex.size();
    int index=0;
    m_generatorPtrVect.reserve(m_numberOfGenerators);
    for(
      iterator pos = m_generatorIndex.begin();
      pos != m_generatorIndex.end();
      ++pos
    ){
      pos->second=index++;
      m_generatorPtrVect.push_back(&(pos->first));
    }
  }

  // --------------------------------------------------------------- //
  friend void swap(FreeModule& A_fm1,FreeModule& A_fm2){
    std::swap(A_fm1.m_generatorIndex,A_fm2.m_generatorIndex);
    std::swap(A_fm1.m_generatorPtrVect,A_fm2.m_generatorPtrVect);
    std::swap(A_fm1.m_numberOfGenerators,A_fm2.m_numberOfGenerators);
  }

  // --------------------------------------------------------------- //
  friend std::ostream& operator<<(std::ostream& out,const FreeModule& A_freeModule){
    out << "Free Module with " << A_freeModule.m_numberOfGenerators <<  " generators\n";
    for(int i=0;i<A_freeModule.m_numberOfGenerators;++i){
      out << i << ") " << *A_freeModule.m_generatorPtrVect[i] << std::endl;
    }
    return out;
  }

  // --------------------------------------------------------------- //
  // Return the index of a generator
  // throw an exception if not found
  int index(const generatorType A_generator) const{
    const_iterator where=m_generatorIndex.find(A_generator);
    if(where!=m_generatorIndex.end()) return where->second;
    throw std::runtime_error("FreeModule::index: generator does not exist");
  }

  // --------------------------------------------------------------- //
  // Find the index of a generator and return it via A_index
  // Return false if not found
  bool findIndex(const generatorType A_generator, int& A_index) const{
    const_iterator where=m_generatorIndex.find(A_generator);
    if(where!=m_generatorIndex.end()){
      A_index=where->second;
      return true;
    }
    return false;
  }

  // --------------------------------------------------------------- //
  // Construct the coef vaector of an element in the chain form
  template<typename P_Chain>
  void coefVector(const P_Chain& A_chain,ColumnVectorType& A_coefVector) const{
    A_coefVector=ColumnVectorType(m_numberOfGenerators);
    for(int i=0;i<m_numberOfGenerators;++i){
      typename P_Chain::const_iterator it=A_chain.find(*m_generatorPtrVect[i]);
      A_coefVector[i]=(it!=A_chain.end() ? it->second : ScalarType(0));
    }
  }

  // --------------------------------------------------------------- //
  int numberOfGenerators() const{
    return m_numberOfGenerators;
  }

  // --------------------------------------------------------------- //
  const_iterator begin() const{
    return m_generatorIndex.begin();
  }

  // --------------------------------------------------------------- //
  const_iterator end() const{
    return m_generatorIndex.end();
  }

  // --------------------------------------------------------------- //
  const generatorType& operator[](int i) const{
    return *(m_generatorPtrVect[i]);
  }

private:
  std::map<generatorType,IntType> m_generatorIndex;
  std::vector<const generatorType*> m_generatorPtrVect;
  int m_numberOfGenerators;
};// ********** class FreeModule ********** //

#endif //_FREEMODULE_H_
/// @}

