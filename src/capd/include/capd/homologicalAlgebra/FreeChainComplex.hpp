/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FreeChainComplex.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_FREECHAINCOMPLEX_HPP_)
#define _FREECHAINCOMPLEX_HPP_

// -------------------------------------------------------------------------------------- //
// ********** FreeChainComplex<freeModuleType>(std::vector<GeneratorType>&) ********** //
/*
  This constructor takes a vector of generators as the argument.
  The generators are assumed to know all their faces by providing the method primaryFaces()
  returning the vector of primary faces
  as well as the method boundary() returning the map mapping primary faces to their coefficients
  in the boundary
  Faces of all generators are assumed to be generators too.
  They are added to the list of generators automatically, so there is no need to add them
  to the input vector

  Warning: changed to a method template - this way one can make class specialization for
  Z generators without forcing compilation of this method for Z generators
  In practice GeneratorType2=GeneratorType.
*/
template<typename freeModuleType>
template<typename GeneratorType2>
FreeChainComplex<freeModuleType>::FreeChainComplex(
  const std::vector<GeneratorType2>& A_gens // list of generators
){
  if(A_gens.size()==0){
    m_topDim=-1;
    return;
  }
  const int topDim= m_topDim= A_gens[0].embeddingDimension();
  // First we reserve space and call implicit constructor for all chain modules
  m_chainModule.reserve(topDim+1);
  m_chainModule.assign(topDim+1,FreeModule<GeneratorType,MatrixType>());
  m_boundaryHomomorphism.reserve(topDim+1);
  m_boundaryHomomorphism.assign(topDim+1,FreeModuleHomomorphism<GeneratorType,MatrixType>());
  // We need a vector of maps to store generators in respective dimensions.
  // Each vector element will be then used to construct a FreeModule and swap it
  // with the FreeModules in  m_chainModule
  std::vector< std::map<GeneratorType,int> > generators(topDim+1);
  // We first dispatch the generators of dimension i to generators[i]
  for(int i=0;i<(int)A_gens.size();++i){
    int d=A_gens[i].dimension();
    generators[d].insert(std::make_pair(A_gens[i],0)); // The zero argument is for the moment only a placeholder
  }
  // Next we generate and dispatch all faces
  for(int q=topDim;q>0;--q){
    for(
      typename std::map<GeneratorType,int>::iterator pos = generators[q].begin();
      pos != generators[q].end();
      ++pos
    ){
      std::vector<ElementaryCube> faces;
      (pos->first).primaryFaces(faces);
      for(int i=0;i<(int)faces.size();++i){
        int d=(pos->first).dimension();
        generators[d-1].insert(std::make_pair(faces[i],0)); // The zero argument is for the moment only a placeholder
      }
    }
  }
  // Now we generate the chain modules in each dimension
  // by making a free module based on i-dimensional generators and swapping
  // it with m_chainModule[i]
  for(int q=0;q<topDim+1;++q){
    FreeModule<GeneratorType,MatrixType> fm(generators[q]);
    swap(m_chainModule[q],fm);
  }
  // And finally we compute the boundary map
  for(int q=topDim;q>0;--q){ // for every dimension
    MatrixType bdryMatrix(
       m_chainModule[q-1].numberOfGenerators(),
       m_chainModule[q].numberOfGenerators()
     );
    for( // for every generator in the domain
      typename std::map<GeneratorType,int>::const_iterator pos = m_chainModule[q].begin();
      pos != m_chainModule[q].end();
      ++pos
    ){
      GeneratorType aGenerator=pos->first;
      int j=pos->second;
      std::map<GeneratorType,int> boundaryChain;
      aGenerator.boundary(boundaryChain);
      for( // for every generator in the boundary of aGenerator
        std::map<ElementaryCube,int>::const_iterator it = boundaryChain.begin();
        it != boundaryChain.end();
        ++it
      ){
        int i=m_chainModule[q-1].index(it->first);
        bdryMatrix[i][j]=it->second;
      } // end for every generator in the boundary of aGenerator
    } // end for every generator in the domain
    // Now we assign the value of m_boundaryHomomorphism[i]
    // by swapping it with a FreeModuleHomomorphism build from the constructed matrix
    FreeModuleHomomorphism<GeneratorType,MatrixType> fmh(
      &m_chainModule[q],
      &m_chainModule[q-1],
      bdryMatrix
    );
    swap(m_boundaryHomomorphism[q],fmh);
  } // end for every dimension
}  // ********** FreeChainComplex<freeModuleType>(std::vector<GeneratorType>&) ********** //

// -------------------------------------------------------------------------------------- //

// ********** FreeChainComplex<freeModuleType>(std::set<GeneratorType>&) ********** //
/*
  This constructor takes a set of generators as the argument.
  The generators are assumed to provide the method boundary()
  returning the map mapping primary faces to their coefficients in the boundary
  Faces of generators are not automatically assumed to be generators in the chain complex, so
  all generators must be listed.
  The algebraic boundaty in the chain module is taken to consists only of the faces present
  in the provided set. For this reason (search), set is taken here as the proper data structure
  on input
  No check is made if the provided set of generators leads to a correct chain complex!!! - should be changed!!!
*/
template<typename freeModuleType>
template<typename GeneratorType2>
FreeChainComplex<freeModuleType>::FreeChainComplex(
  const std::set<GeneratorType2>& A_gensSet // set of generators
){
  typedef typename freeModuleType::GeneratorType GeneratorType;
  if(A_gensSet.size()==0){
    m_topDim=-1;
    return;
  }
  typename std::set<GeneratorType2>::const_iterator it=A_gensSet.begin();
//  const int topDim= m_topDim= it->embeddingDimension();  // embeddingDimension is obsolete
  const int topDim= m_topDim= it->embDim();
  // First we reserve space and call implicit constructor for all chain modules
  m_chainModule.reserve(topDim+1);
  m_chainModule.assign(topDim+1,FreeModule<GeneratorType,MatrixType>());
  m_boundaryHomomorphism.reserve(topDim+1);
  m_boundaryHomomorphism.assign(topDim+1,FreeModuleHomomorphism<GeneratorType,MatrixType>());
  // We need a vector of maps to store generators in respective dimensions.
  // Each vector element will be then used to construct a FreeModule and swap it
  // with the FreeModules in  m_chainModule
  std::vector< std::map<GeneratorType,int> > generators(topDim+1);
  // We first dispatch thegenerators of dimension i to generators[i]
  for(it=A_gensSet.begin();it!=A_gensSet.end();++it){
//    int d=it->dimension(); // dimension is obsolete
    int d=it->ownDim();
    generators[d].insert(std::make_pair(*it,0)); // The zero argument at this stage is only a placeholder
  }
  // Now we generate the chain modules in each dimension
  // by making a free module based on i-dimensional generators and swapping
  // it with m_chainModule[i]
  for(int q=0;q<topDim+1;++q){
    FreeModule<GeneratorType,MatrixType> fm(generators[q]);
    swap(m_chainModule[q],fm);
  }
  // And finally we compute the boundary map
  for(int q=topDim;q>0;--q){ // for every dimension
    MatrixType bdryMatrix(
       m_chainModule[q-1].numberOfGenerators(),
       m_chainModule[q].numberOfGenerators()
     );
    for( // for every generator in the domain
      typename std::map<GeneratorType,int>::const_iterator pos = m_chainModule[q].begin();
      pos != m_chainModule[q].end();
      ++pos
    ){
      GeneratorType aGenerator=pos->first;
      int j=pos->second;
      std::map<GeneratorType,int> boundaryChain;
      aGenerator.boundary(boundaryChain);
      for( // for every generator in the boundary of aGenerator
        typename std::map<GeneratorType,int>::const_iterator it = boundaryChain.begin();
        it != boundaryChain.end();
        ++it
      ){
        int i;
        // We add to the chain boundary matrix only these generators,
        // which are present in the chain module
        if(m_chainModule[q-1].findIndex(it->first,i)){
          bdryMatrix[i][j]=it->second;
        }
      } // end for every generator in the boundary of aGenerator
    } // end for every generator in the domain
    // Now we assign the value of m_boundaryHomomorphism[i]
    // by swapping it with a FreeModuleHomomorphism build from the constructed matrix
    FreeModuleHomomorphism<GeneratorType,MatrixType> fmh(
      &m_chainModule[q],
      &m_chainModule[q-1],
      bdryMatrix
    );
    swap(m_boundaryHomomorphism[q],fmh);
  } // end for every dimension
}  // ********** FreeChainComplex<freeModuleType>(std::set<GeneratorType>&) ********** //

template<typename freeModuleType>
std::ostream& operator<<(std::ostream& out, const FreeChainComplex<freeModuleType>& A_fCC){
  out << "--- Free Chain Complex ---" << std::endl;
  for(int i=0;i<A_fCC.m_topDim+1;++i){
    out << "  Dimension " << i << std::endl;
    out << A_fCC.m_chainModule[i];
    out << "    Boundary Matrix " << std::endl;
    out << A_fCC.m_boundaryHomomorphism[i].coefMatrix() << std::endl;
  }
  return out;
}


#endif //_FREECHAINCOMPLEX_HPP_
/// @}

