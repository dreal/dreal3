/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ReducibleFreeChainComplex.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_REDUCIBLEFREECHAINCOMPLEX_HPP_)
#define _REDUCIBLEFREECHAINCOMPLEX_HPP_

#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.h"
#include "capd/auxil/Stopwatch.h"
#include <functional>


// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
template<typename freeModuleType2>
ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::ReducibleFreeChainComplex(
  const FreeChainComplex<freeModuleType2>& fcc
):m_storeReducedPairs(false){
  try{
    for(int q=0;q<=fcc.topDim();++q){ // for every grade dimension
      // prepare an empty map of generator boundaries for this dimension
      m_ggb.push_back(GeneratorBoundaries());
      // prepare an empty map of generator coboundaries for this dimension
      m_ggCb.push_back(GeneratorCoBoundaries());
      const MatrixType& bdMtrx=fcc.boundaryHomomorphism(q).coefMatrix();
      int m=bdMtrx.numberOfRows();
      int n=fcc.chainModule(q).numberOfGenerators();
      for(int j=0;j<n;++j){ // for every generator in grade q
        // prepare an empty map for the boundary of this generator
        m_ggb[q].insert(std::make_pair(j,Chain()));
        // prepare an empty map for the coboundary of this generator
        m_ggCb[q].insert(std::make_pair(j,Chain()));
        //
        if(q>0) // for grade zero boundary is assumed to be always zero - this may require a change in future generalizations
        for(int i=0;i<m;++i){ // for every generator in grade q-1
          if(bdMtrx[i][j]!=ScalarType(0)){
            // the boundary of the j-th generator in q-th dimension has coefficient bdMtrx[i][j] for i-th generator in dimension q-1:
            m_ggb[q][j].insert(std::make_pair(i,bdMtrx[i][j]));
            // the coboundary of the i-th generator in (q-1)-th dimension has coefficient bdMtrx[i][j] for j-th generator in dimension q
            m_ggCb[q-1][i].insert(std::make_pair(j,bdMtrx[i][j]));
          }
        }// end for int i;
      }// end for int j;
    }// end for int q;
  }catch(std::bad_alloc& e){
    throw std::runtime_error("Memory request for ReducibleFreeChainComplex failed");
  }
}


// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
template<typename GeneratorType2>
ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::ReducibleFreeChainComplex(
  const std::vector<GeneratorType2>& A_gens // vector of generators
):m_storeReducedPairs(false){
  try{
Stopwatch sw;
    if(A_gens.size()==0) return;
    typename std::vector<GeneratorType2>::const_iterator it=A_gens.begin();
    const int topDim=it->embeddingDimension();
    m_ggb.reserve(1+topDim);
    m_ggCb.reserve(1+topDim);
    for(int q=0;q<=topDim;++q){ // for every grade dimension
      // prepare an empty map of generator boundaries for this dimension
      m_ggb.push_back(GeneratorBoundaries());
      // prepare an empty map of generator coboundaries for this dimension
      m_ggCb.push_back(GeneratorCoBoundaries());
    }
    // We need a vector of maps to store generator codes in respective dimensions.
    std::vector< std::map<GeneratorType2,GeneratorCode> > generators(topDim+1);
    // We first dispatch the generators of dimension i to generators[i]
    // The codes assigned are just the consecutive numbers for each dimesion, as the generators are read from A_gens
    for(it=A_gens.begin();it!=A_gens.end();++it){
      int d=it->dimension();
      GeneratorCode code=generators[d].size(); // The current size becomes the code for the next generator
      generators[d].insert(std::make_pair(*it,code));
      // prepare an empty map for the boundary of this generator
      m_ggb[d].insert(std::make_pair(code,Chain()));
      // prepare an empty map for the coboundary of this generator
      m_ggCb[d].insert(std::make_pair(code,Chain()));
    }
std::cout << "Codes assigned in " << sw << std::endl;

    // After the codes are assigned we can compute the boundary map
    for(int q=topDim;q>0;--q){ // for every dimension
std::cout << "Computing boundary in dim  " << q << std::endl;
      for( // for every generator in the domain
        typename std::map<GeneratorType2,GeneratorCode>::const_iterator pos = generators[q].begin();
        pos != generators[q].end();
        ++pos
      ){
        const GeneratorType2& aGenerator=pos->first;
        const GeneratorCode& code=pos->second;
        std::map<GeneratorType2,int> boundaryChain;
        aGenerator.boundary(boundaryChain);
        for( // for every generator in the boundary of aGenerator
          typename std::map<GeneratorType2,int>::const_iterator it = boundaryChain.begin();
          it != boundaryChain.end();
          ++it
        ){
          const GeneratorType2& aGeneratorBdyFace=it->first;

          // If such a face is not yet in generators[q-1], add it and make suitable places for its codes
          // in m_ggb[q-1] and m_ggCb[q-1]
          if(!generators[q-1].count(aGeneratorBdyFace)){
            GeneratorCode code=generators[q-1].size(); // The current size becomes the code for the next generator
            generators[q-1].insert(std::make_pair(aGeneratorBdyFace,code));
            // prepare an empty map for the boundary of this generator
            m_ggb[q-1].insert(std::make_pair(code,Chain()));
            // prepare an empty map for the coboundary of this generator
            m_ggCb[q-1].insert(std::make_pair(code,Chain()));

          }

          const GeneratorCode& aGeneratorBdyFaceCode=generators[q-1][aGeneratorBdyFace];
          const int& coef=it->second;
          if(coef!=0){
            // the boundary of the code-th generator in q-th dimension has coefficient coef for aGeneratorBdyFaceCode-th generator in dimension q-1:
            m_ggb[q][code].insert(std::make_pair(aGeneratorBdyFaceCode,coef));
            // the coboundary of the aGeneratorBdyFaceCode-th generator in (q-1)-th dimension has coefficient coef for code-th generator in dimension q
            m_ggCb[q-1][aGeneratorBdyFaceCode].insert(std::make_pair(code,coef));
          }
        } // end for every generator in the boundary of aGenerator
      } // end for every generator in the domain
    } // end for every dimension
  }catch(std::bad_alloc& e){
    throw std::runtime_error("Memory request for ReducibleFreeChainComplex from vector<GeneratorType2> failed");
  }
}  // ********** ReducibleFreeChainComplex<freeModuleType,GeneratorCode>(std::vector<GeneratorType2>&) ********** //

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
template<typename GeneratorType2>
ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::ReducibleFreeChainComplex(
  const std::set<GeneratorType2>& A_gensSet // set of generators
):m_storeReducedPairs(false){
  try{
    if(A_gensSet.size()==0) return;
    typename std::set<GeneratorType2>::const_iterator it=A_gensSet.begin();
    const int topDim=it->embDim();
    std::vector<int> codeCounters;
    for(int q=0;q<=topDim;++q){ // for every grade dimension
      // prepare an empty map of generator boundaries for this dimension
      m_ggb.push_back(GeneratorBoundaries());
      // prepare an empty map of generator coboundaries for this dimension
      m_ggCb.push_back(GeneratorCoBoundaries());
      codeCounters.push_back(0);
    }
    // We need a vector of maps to store generator codes in respective dimensions.
    std::vector< std::map<GeneratorType2,GeneratorCode> > generators(topDim+1);
    // We first dispatch the generators of dimension i to generators[i]
    // The codes assigned are just the consecutive numbers for each dimesion, as the generators are read from A_gensSet
    for(it=A_gensSet.begin();it!=A_gensSet.end();++it){
      int d=it->ownDim();
      // -- MM std::cout << "Dispatching " << *it << " of dim " << d  << std::endl;
//      GeneratorCode code=generators[d].size();       // The current size becomes the code for the next generator
      GeneratorCode code=codeCounters[d]++;       // The current size becomes the code for the next generator
      generators[d].insert(std::make_pair(*it,code));
      // prepare an empty map for the boundary of this generator
      m_ggb[d].insert(std::make_pair(code,Chain()));
      // prepare an empty map for the coboundary of this generator
      m_ggCb[d].insert(std::make_pair(code,Chain()));
    }

    // After the codes are assigned we can compute the boundary map
    for(int q=topDim;q>0;--q){ // for every dimension
      // -- MM  std::cout << "dim=" << q << std::endl;   // -- MM
      for( // for every generator in the domain
        typename std::map<GeneratorType2,GeneratorCode>::const_iterator pos = generators[q].begin();
        pos != generators[q].end();
        ++pos
      ){
        const GeneratorType2& aGenerator=pos->first;
        const GeneratorCode& code=pos->second;
        ChainT<std::map<GeneratorType2,ScalarType> > boundaryChain;
//        std::map<GeneratorType2,int> boundaryChain;
        // -- MM  std::cout << "  at domain generator " << pos->first << "'" << pos->second << std::endl;

        aGenerator.boundary(boundaryChain);
        for( // for every generator in the boundary of aGenerator
          typename std::map<GeneratorType2,int>::const_iterator it = boundaryChain.begin();
          it != boundaryChain.end();
          ++it
        ){
          const GeneratorType2& aGeneratorBdyFace=it->first;
          // -- MM  std::cout << "     at bdy generator " << it->first << std::endl;
          // We disregard the generators in the boundary, which are not in the list of generators obtained from the set A_gensSet
          // because we assume the algebraic boundary consists only of the generators present in the set
          if(!generators[q-1].count(aGeneratorBdyFace)) continue;
          const GeneratorCode& aGeneratorBdyFaceCode=generators[q-1][aGeneratorBdyFace];
          const int& coef=it->second;
          if(coef!=0){
            // the boundary of the code-th generator in q-th dimension has coefficient coef for aGeneratorBdyFaceCode-th generator in dimension q-1:
            m_ggb[q][code].insert(std::make_pair(aGeneratorBdyFaceCode,coef));
            // the coboundary of the aGeneratorBdyFaceCode-th generator in (q-1)-th dimension has coefficient coef for code-th generator in dimension q
            m_ggCb[q-1][aGeneratorBdyFaceCode].insert(std::make_pair(code,coef));
          }
        } // end for every generator in the boundary of aGenerator
      } // end for every generator in the domain
    } // end for every dimension
  }catch(std::bad_alloc& e){
    throw std::runtime_error("Memory request for ReducibleFreeChainComplex from set<GeneratorType2> failed");
  }
}  // ********** ReducibleFreeChainComplex<freeModuleType,GeneratorCode>(std::set<GeneratorType2>&) ********** //

// ------------------------------------------------------------ //

// This is now the main constructor used to construct RFCC from sets
template<typename freeModuleType, typename P_GeneratorCode>
template<typename P_Set>
ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::ReducibleFreeChainComplex(
  const P_Set& A_set, // a set accessible via iterators
  int A_storeReducedPairs
):m_storeReducedPairs(A_storeReducedPairs){
  try{
    if(A_set.cardinality()==0) return;
    typename P_Set::PointCoordIterator it=A_set.begin();
    const int topDim=A_set.embDim();

    for(int q=0;q<=topDim;++q){ // for every grade dimension
      // prepare an empty map of generator boundaries for this dimension
      m_ggb.push_back(GeneratorBoundaries());
      // prepare an empty map of generator coboundaries for this dimension
      m_ggCb.push_back(GeneratorCoBoundaries());
    }
    // We need a vector of maps to store generator codes in respective dimensions.
    std::vector< std::set<GeneratorType> > generators(topDim+1);
    // We first dispatch the generators of dimension i to generators[i]
    for(it=A_set.begin();it!=A_set.end();++it){
      GeneratorType gen(it);
      int d=gen.ownDim();
      generators[d].insert(gen);
      // prepare an empty map for the boundary of this generator
      m_ggb[d].insert(std::make_pair(gen,Chain()));
      // prepare an empty map for the coboundary of this generator
      m_ggCb[d].insert(std::make_pair(gen,Chain()));
    }

    // After the codes are assigned we can compute the boundary map
    for(int q=topDim;q>0;--q){ // for every dimension
      for( // for every generator in the domain
        typename std::set<GeneratorType>::const_iterator pos = generators[q].begin();
        pos != generators[q].end();
        ++pos
      ){
        const GeneratorType& aGenerator=*pos;
//        std::map<GeneratorType,ScalarType> boundaryChain;
        Chain boundaryChain;
        aGenerator.boundary(boundaryChain);
        for( // for every generator in the boundary of aGenerator
          typename std::map<GeneratorType,ScalarType>::const_iterator it = boundaryChain.begin();
          it != boundaryChain.end();
          ++it
        ){
          const GeneratorType& aGeneratorBdyFace=it->first;
          // We disregard the generators in the boundary, which are not in the list of generators obtained from the set A_gensSet
          // because we assume the algebraic boundary consists only of the generators present in the set
          typename std::set<GeneratorType>::const_iterator itFound=generators[q-1].find(aGeneratorBdyFace);
          if( itFound == generators[q-1].end() ) continue;
//          const int& coef=it->second;
          const ScalarType& coef=it->second;
          if(coef!=0){
            // the boundary of the code-th generator in q-th dimension has coefficient coef for aGeneratorBdyFace-th generator in dimension q-1:
            m_ggb[q][aGenerator].insert(std::make_pair(aGeneratorBdyFace,coef));
            // the coboundary of the aGeneratorBdyFace-th generator in (q-1)-th dimension has coefficient coef for aGenerator-th generator in dimension q
            m_ggCb[q-1][aGeneratorBdyFace].insert(std::make_pair(aGenerator,coef));
          }
        } // end for every generator in the boundary of aGenerator
      } // end for every generator in the domain
    } // end for every dimension
  }catch(std::bad_alloc& e){
    throw std::runtime_error("Memory request for ReducibleFreeChainComplex from set<GeneratorType2> failed");
  }
}  // ********** ReducibleFreeChainComplex<freeModuleType,GeneratorType>(std::set<GeneratorType2>&) ********** //

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::operator FreeChainComplex<freeModuleType>(){
  FreeChainComplex<freeModuleType> result;
  result.m_topDim=m_ggb.size()-1;
  if(result.m_topDim<0) return result;
  // First we reserve space and call implicit constructor for all chain modules
  result.m_chainModule.reserve(result.m_topDim+1);
  result.m_chainModule.assign(result.m_topDim+1,freeModuleType());
  result.m_boundaryHomomorphism.reserve(result.m_topDim+1);
  result.m_boundaryHomomorphism.assign(result.m_topDim+1,FreeModuleHomomorphism<GeneratorCode,MatrixType>());
  // We need a vector of maps to store generators in respective dimensions.
  // Each vector element will be then used to construct a FreeModule and swap it
  // with the FreeModules in  m_chainModule
  // Below we need int, not ScalarType, because this is not a coefficient, but placeholder for generator number
  std::vector< std::map<GeneratorCode,int> > generators(result.m_topDim+1);
  // Next we generate all faces
  for(int q=0;q<=result.m_topDim;++q){
    for(
      typename GeneratorBoundaries::iterator pos = m_ggb[q].begin();
      pos != m_ggb[q].end();
      ++pos
    ){
      generators[q].insert(std::make_pair(pos->first,0));
    }
  }

  // We first generate the chain modules in each dimension
  // by making a free module based on i-dimensional generators and swapping
  // it with m_chainModule[i]
  for(int q=0;q<result.m_topDim+1;++q){
    FreeModule<GeneratorCode,MatrixType> fm(generators[q]);
    swap(result.m_chainModule[q],fm);
  }
  // And finally we compute the boundary map
  for(int q=result.m_topDim;q>0;--q){ // for every dimension
    MatrixType bdryMatrix(
       result.m_chainModule[q-1].numberOfGenerators(),
       result.m_chainModule[q].numberOfGenerators()
     );
    for( // for every generator in the domain
      typename std::map<GeneratorCode,int>::const_iterator pos = result.m_chainModule[q].begin();
      pos != result.m_chainModule[q].end();
      ++pos
    ){
      GeneratorCode argFaceCode=pos->first;
      for( // for every generator in the codomain
        typename std::map<GeneratorCode,int>::const_iterator pos2 = result.m_chainModule[q-1].begin();
        pos2 != result.m_chainModule[q-1].end();
        ++pos2
      ){
        int i=pos2->second;
        int j=pos->second;
        GeneratorCode bdFaceCode=pos2->first;
        bdryMatrix[i][j]=( m_ggb[q][argFaceCode].count(bdFaceCode) ? m_ggb[q][argFaceCode][bdFaceCode] : ScalarType(0) );
      } // end for every generator in the codomain
    } // end for every generator in the domain
    // Now we assign the value of m_boundaryHomomorphism[i]
    // by swapping it with a FreeModuleHomomorphism build from the constructed matrix
    FreeModuleHomomorphism<GeneratorCode,MatrixType> fmh(
      &result.m_chainModule[q],
      &result.m_chainModule[q-1],
      bdryMatrix
    );
    swap(result.m_boundaryHomomorphism[q],fmh);
  } // end for every dimension
  return result;
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
void ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::reducePair(
  // grade in which the reduction is performed
  int q,
  // iterator pointing to the first element of the reduction pair (b,a) or (coFace,face)
  // pointing to the external map
  typename GeneratorBoundaries::iterator coFacePos,
  // iterator pointing to the second element of the reduction pair (b,a) or (coFace,face)
  // pointing to the map storing the boundary of generator b
  typename Chain::iterator facePos
){
  // these are shorthands
  int topDim=m_ggb.size()-1;
  GeneratorCode b=coFacePos->first;
  GeneratorCode a=facePos->first;

  Chain& bBdry=coFacePos->second;
  CoChain& aCoBdry=m_ggCb[q-1][a];

  ScalarType bBdryCoefAt_a=facePos->second;
  // Added 2010-06-05 for compatibility with other coefficient rings
  // For integers the inverse of an integer equals the integer, so inverse was not used earlier
  ScalarType inv_bBdryCoefAt_a=inverse(bBdryCoefAt_a);

  if(m_storeReducedPairs){
    // -- fcout << " RFCC Storing reducible pair (" << b << "," << a << ")\n"; //--
    // Changed 2010-06-05 for compatibility with other coefficient rings
    // Does not matter for integers, for other coefficients not tested yet
    m_reducedPairs.push_back(ReducedPair(q,b,a,bBdry,aCoBdry,inv_bBdryCoefAt_a));
//    m_reducedPairs.push_back(ReducedPair(q,b,a,bBdry,aCoBdry,bBdryCoefAt_a));
  }

  // Remove b from boundries of generators in grade q+1
  if(q<topDim){
    for( // every generator in the coboundary of b
      typename CoChain::iterator pos = m_ggCb[q][b].begin();
      pos != m_ggCb[q][b].end();
      ++pos
    ){
      const GeneratorCode& c=pos->first;
      m_ggb[q+1][c].erase(b);
    }
  }

  // Remove a from coboundries of generators in grade q-2
  if(q>1){
    for( // every generator in the boundary of a
      typename Chain::iterator pos = m_ggb[q-1][a].begin();
      pos != m_ggb[q-1][a].end();
      ++pos
    ){
      const GeneratorCode& c=pos->first;
      m_ggCb[q-2][c].erase(a);
    }
  }

  // update coboundaries of (q-1) dimensional generators in the boundary of b
  for(
    typename Chain::iterator ChainIt=bBdry.begin();
    ChainIt != bBdry.end();
    ++ChainIt
  ){
    const GeneratorCode& c=ChainIt->first;
    if(c==a) continue;
    ScalarType& bBdryCoefAt_c=ChainIt->second;
    CoChain& cCoBdry=m_ggCb[q-1][c];
//    cCoBdry+=-bBdryCoefAt_a*bBdryCoefAt_c*aCoBdry;
    cCoBdry+=-inv_bBdryCoefAt_a*bBdryCoefAt_c*aCoBdry;
  }


  // update boundaries of q dimensional generators in the coboundary of a
  for( // every generator in the coboundary of a
    typename CoChain::iterator pos = m_ggCb[q-1][a].begin();
    pos != m_ggCb[q-1][a].end();
    ++pos
  ){
    const GeneratorCode& e=pos->first;
    if(e==b) continue;
    // shorthand for the the boundary of e
    Chain& eBdry=m_ggb[q][e];
    ScalarType& eBdryCoefAt_a=eBdry[a];  // shorthand for coefficient
    // compute the new boundary coefficients
//    eBdry+=-bBdryCoefAt_a*eBdryCoefAt_a*bBdry;
    eBdry+=-inv_bBdryCoefAt_a*eBdryCoefAt_a*bBdry;

  }

  // remove b and a from boundaries lists (together with their boundaries)
  m_ggb[q].erase(coFacePos);
  m_ggb[q-1].erase(a);
  // remove b and a from coboundaries lists (together with their boundaries)
  m_ggCb[q].erase(b);
  m_ggCb[q-1].erase(a);
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
int ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::reduce(){
  int pairsReduced=0;
  int topDim=m_ggb.size()-1;
  for(int q=topDim;q>0;--q){
    SearchReduciblePair:

    int ct1=0;
    for( // every generator in grade q
      typename GeneratorBoundaries::iterator pos = m_ggb[q].begin();
      pos != m_ggb[q].end();
      ++pos
    ){
      ++ct1;
      int ct2=0;
      for( // every generator in the boundary
        typename Chain::iterator pos2 = (pos->second).begin();
        pos2 != (pos->second).end();
        ++pos2
      ){
        ++ct2;
        // do reduction if the coefficient is 1 or -1
//        if( ScalarType(std::abs(pos2->second)) == ScalarType(1) ){
        if( isInvertible(ScalarType(pos2->second)) ){
          ++pairsReduced;
          reducePair(q,pos,pos2);
          goto SearchReduciblePair; // the maps have changed, iterators are no longer valid,
                                    // so do not continue, start again
        }
      }
    }
  }
  return pairsReduced;
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
int ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::findMeasure(const int& coFaceDim,const P_GeneratorCode& coFace, const P_GeneratorCode& face){
  if (m_ggb[coFaceDim][coFace].size()<=0){
    std::ostringstream s;
    s << "Bad measure for pair " << coFace << " " << face << ". Boundary of coface is " << m_ggb[coFaceDim][coFace].size() << "\n";
    throw s.str();
  }
  if (m_ggCb[coFaceDim-1][face].size()<=0){
    std::ostringstream s;
    s << "Bad measure for pair " << coFaceDim << "_" << coFace << " " << coFaceDim-1 << "_" << face << std::endl;
    s << "Coboundary of face is " << m_ggCb[coFaceDim-1][face].size() << "\n";
    s << "Bundary of coface is " << m_ggb[coFaceDim][coFace].size() << "\n";
    throw s.str();
  }
  return (m_ggb[coFaceDim][coFace].size()-1)*(m_ggCb[coFaceDim-1][face].size()-1);
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
void ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::extractReduciblePairsInVicinityOf(
  int dim,
  P_GeneratorCode g,
  std::set<ReduciblePair>& source,
  std::list<ReduciblePair>& destination
){
  if(dim>0){
    Chain& bdy=m_ggb[dim][g];
    for( // every generator in the boundary
      typename Chain::iterator faceIt = bdy.begin();
      faceIt != bdy.end();
      ++faceIt
    ){
      const GeneratorCode& gFace=faceIt->first;
      CoChain& gFaceCbdy=m_ggCb[dim-1][gFace];
      for( // every generator in the coboundary
        typename CoChain::iterator coFaceIt = gFaceCbdy.begin();
        coFaceIt != gFaceCbdy.end();
        ++coFaceIt
      ){
        const GeneratorCode& coFace=coFaceIt->first;
        int m=findMeasure(dim,coFace,gFace);
        ReduciblePair p(dim,coFace,gFace,m);
        int e=source.erase(p);
        if(e) destination.push_back(p);
      }
    }
  }
  int topDim=m_ggb.size()-1;
  if(dim<topDim){
    CoChain& cBdy=m_ggCb[dim][g];
    for( // every generator in the coboundary
      typename CoChain::iterator coFaceIt = cBdy.begin();
      coFaceIt != cBdy.end();
      ++coFaceIt
    ){
      const GeneratorCode& gCoFace=coFaceIt->first;
      Chain& gCoFaceBdy=m_ggb[dim+1][gCoFace];
      for( // every generator in the boundary
        typename Chain::iterator faceIt = gCoFaceBdy.begin();
        faceIt != gCoFaceBdy.end();
        ++faceIt
      ){
        const GeneratorCode& face=faceIt->first;
        int m=findMeasure(dim+1,gCoFace,face);
        ReduciblePair p(dim+1,gCoFace,face,m);
        int e=source.erase(p);
        if(e) destination.push_back(p);
      }
    }
  }
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
int ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::reduceViaSort(){

  int pairsReduced=0;

  std::set<ReduciblePair> reduciblePairPriorityQueue;
  int topDim=m_ggb.size()-1;

  int pass=0;
  while(true){ // while any reducible pairs are available
  ++pass;
    int reduciblePairsCount=0;
    for(int q=topDim;q>0;--q){
      for( // every generator in grade q
        typename GeneratorBoundaries::iterator coFaceIt = m_ggb[q].begin();
        coFaceIt != m_ggb[q].end();
        ++coFaceIt
      ){
        for( // every generator in the boundary
          typename Chain::iterator faceIt = (coFaceIt->second).begin();
          faceIt != (coFaceIt->second).end();
          ++faceIt
        ){
          // when the coefficient is not invertible, continue search
          if( std::abs(faceIt->second) != ScalarType(1) ) continue;
          // add the reducible pair to the queue
          int m=findMeasure(q,coFaceIt->first,faceIt->first);
          reduciblePairPriorityQueue.insert(ReduciblePair(q,coFaceIt->first,faceIt->first,m));
          ++reduciblePairsCount;
        }
      }
    }

    if(!reduciblePairsCount) break; // no more reducible pairs, transfer to Smith

    while(!reduciblePairPriorityQueue.empty()){
      // remove the first element of the queue
      ReduciblePair rp(*reduciblePairPriorityQueue.begin());
      //
      const GeneratorCode& coFace=rp.CoFace();
      const GeneratorCode& face=rp.Face();
      int q=rp.CoFaceDim();
      std::list<ReduciblePair> reduciblePairTemporaryList;
      // extract the reducible pairs whose measure can change
      extractReduciblePairsInVicinityOf(
        q,
        coFace,
        reduciblePairPriorityQueue,
        reduciblePairTemporaryList
      );
      extractReduciblePairsInVicinityOf(
        q-1,
        face,
        reduciblePairPriorityQueue,
        reduciblePairTemporaryList
      );
      typename GeneratorBoundaries::iterator coFaceIt=m_ggb[q].find(coFace);
      typename Chain::iterator faceIt=coFaceIt->second.find(face);

      // Now remove the reducible pair
      reducePair(q,coFaceIt,faceIt);
      ++pairsReduced;
      // And store again the reducible pairs involved
      for( // every stored reducible pair
        typename std::list<ReduciblePair>::iterator rpIt = reduciblePairTemporaryList.begin();
        rpIt != reduciblePairTemporaryList.end();
        ++rpIt
      ){
        const int& q=rpIt->CoFaceDim();
        // skip pairs which are no longer reducible pairs
        typename GeneratorBoundaries::iterator coFaceIt=m_ggb[q].find(rpIt->CoFace());
        if(coFaceIt == m_ggb[q].end()) continue;
        typename Chain::iterator faceIt=coFaceIt->second.find(rpIt->Face());
        if(faceIt == coFaceIt->second.end()) continue;
        if( std::abs(faceIt->second) != ScalarType(1) ) continue;
        // find measure and store the pair back
        int m=findMeasure(q,rpIt->CoFace(),rpIt->Face());
        rpIt->setMeasure(m);
        reduciblePairPriorityQueue.insert(*rpIt);
      }
    }
  }
  // return information if any reducible pair found at all
  return pairsReduced;
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
int ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::reduceViaLocalSort(){
  int pairsReduced=0;
  int topDim=m_ggb.size()-1;
  for(int q=topDim;q>0;--q){ // every dimension starting from the top
    // The highest priority is with the least ordering value, so we use greater instead of less
    std::priority_queue<ReduciblePair,std::deque<ReduciblePair>,std::greater<ReduciblePair> > candidates;
    while(true){
      for( // every generator in grade q
        typename GeneratorBoundaries::iterator coFacePos = m_ggb[q].begin();
        coFacePos != m_ggb[q].end();
        ++coFacePos
      ){
        const GeneratorCode& coFace=coFacePos->first;
        for( // every generator in the boundary
          typename Chain::iterator facePos = (coFacePos->second).begin();
          facePos != (coFacePos->second).end();
          ++facePos
        ){
          const GeneratorCode& face=facePos->first;
          // when the coefficient is not invertible, continue search
          if( std::abs(facePos->second) != ScalarType(1) ) continue;
          // reducible pair with requested coboundary size of generator a found,
          // push it on queue and proceed to reductions
          int m=findMeasure(q,coFace,face);
          ReduciblePair p(q,coFace,face,m);
          candidates.push(p);
          goto reduceDeque;
        }
      }
      break; // break the while loop, because no more reducible pairs exist for this q=embDim

      reduceDeque:
      while(!candidates.empty()){
        ReduciblePair p=candidates.top();
        candidates.pop();
        const GeneratorCode& a=p.Face();
        const GeneratorCode& b=p.CoFace();
        typename GeneratorCoBoundaries::iterator aPosIn_ggCb=m_ggCb[q-1].find(a);
        // if a already removed, proceed with the next candidate
        if( aPosIn_ggCb == m_ggCb[q-1].end() ) continue;

        typename GeneratorBoundaries::iterator bPos=m_ggb[q].find(b);
        // if b already removed, proceed with the next candidate
        if( bPos == m_ggb[q].end() ) continue;

        typename Chain::iterator aPos=(bPos->second).find(a);
        // if <bd b,a> is not invertible, proceed with the next candidate
        if( std::abs(aPos->second) != ScalarType(1) ) continue;

        // (b,a) is a reducible pair, so increase the counter
        ++pairsReduced;
        // the pair will be removed, but first the other boundary
        // elements of b will be stored in the queue of candidates:
        // Search in the boundaty of b for candidates for the second element of a reduction pair
        for( // every generator in the boundary
          typename Chain::iterator facePos = (bPos->second).begin();
          facePos != (bPos->second).end();
          ++facePos
        ){
          const GeneratorCode& a1=facePos->first;
          if(a1 == a) continue;
          typename GeneratorCoBoundaries::iterator a1posIn_ggCb=m_ggCb[q-1].find(a1);
          for( // every generator in the coboundary
            typename Chain::iterator coFacePos = (a1posIn_ggCb->second).begin();
            coFacePos != (a1posIn_ggCb->second).end();
            ++coFacePos
          ){
            if( std::abs(coFacePos->second) != ScalarType(1) ) continue;
            int m=findMeasure(q,coFacePos->first,facePos->first);
            ReduciblePair p(q,coFacePos->first,facePos->first,m);
            candidates.push(p);
          }
        }
        // Finally remove the reducible pair
        reducePair(q,bPos,aPos);
      }
    }
  }
  // return the number of pairs reduced
  return pairsReduced;
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
bool ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::reduceViaStack(
  unsigned int searchedCoboundrySize, int& pairsReduced
){
  bool reduciblePairFound=false;
  pairsReduced=0;
  int topDim=m_ggb.size()-1;
  for(int q=topDim;q>0;--q){ // every dimension starting from the top
    std::list<GeneratorCode> subGeneratorsForPotentialReduction;
    for( // every generator in grade q
      typename GeneratorBoundaries::iterator coFacePos = m_ggb[q].begin();
      coFacePos != m_ggb[q].end();
      ++coFacePos
    ){
      for( // every generator in the boundary
        typename Chain::iterator facePos = (coFacePos->second).begin();
        facePos != (coFacePos->second).end();
        ++facePos
      ){
        // when the coefficient is not invertible, continue search
        if( std::abs(facePos->second) != ScalarType(1) ) continue;
        // mark that a reducible pair exists
        reduciblePairFound=true;
        // when the coboundary has incorrect size, continue search
        if(m_ggCb[q-1][facePos->first].size() != searchedCoboundrySize) continue;
        // reducible pair with requested coboundary size of generator a found,
        // push it on queue and proceed to reductions
        subGeneratorsForPotentialReduction.push_back(facePos->first);
        goto reduceDeque;
      }
    }

    reduceDeque:
    while(!subGeneratorsForPotentialReduction.empty()){
      GeneratorCode a=subGeneratorsForPotentialReduction.front();
      subGeneratorsForPotentialReduction.pop_front();
      typename GeneratorCoBoundaries::iterator aPosIn_ggCb=m_ggCb[q-1].find(a);
      // if a already removed, proceed with the next candidate
      if( aPosIn_ggCb == m_ggCb[q-1].end() ) continue;
      // if a coboundary is of wrong size, proceed with the next candidate
      if( (aPosIn_ggCb->second).size() != searchedCoboundrySize) continue;
      typename CoChain::iterator bPosInCbdyOf_a = m_ggCb[q-1][a].begin();
      // if b already removed, proceed with the next candidate
      if( bPosInCbdyOf_a == m_ggCb[q-1][a].end() ) continue;

      GeneratorCode b=bPosInCbdyOf_a->first;
      typename GeneratorBoundaries::iterator bPos=m_ggb[q].find(b);
      typename Chain::iterator aPos=(bPos->second).find(a);
      // if <bd b,a> is not invertible, proceed with the next candidate
      if( std::abs(aPos->second) != ScalarType(1) ) continue;

      // (b,a) is a reducible pair, so increase the counter
      ++pairsReduced;
      // the pair will be removed, but first the other boundary
      // elements of b will be stored in the queue of candidates:
      // Search in the boundaty of b for candidates for the second element of a reduction pair
      for( // every generator in the boundary
        typename Chain::iterator facePos = (bPos->second).begin();
        facePos != (bPos->second).end();
        ++facePos
      ){
        if(facePos->first == a) continue;
        if( std::abs(facePos->second) != ScalarType(1) ) continue;
        subGeneratorsForPotentialReduction.push_back(facePos->first);
      }
      // Finally remove the reducible pair
      reducePair(q,bPos,aPos);
    }
  }
  // return information if any reducible pair found at all
  return reduciblePairFound;
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
void ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::reduceFromBottom(){
  int topDim=m_ggb.size()-1;
  for(int q=1;q<=topDim;++q){
    SearchReduciblePair:

    int ct1=0;
    for( // every generator in grade q
      typename GeneratorBoundaries::iterator pos = m_ggb[q].begin();
      pos != m_ggb[q].end();
      ++pos
    ){
      ++ct1;
      int ct2=0;
      for( // every generator in the boundary
        typename Chain::iterator pos2 = (pos->second).begin();
        pos2 != (pos->second).end();
        ++pos2
      ){
        ++ct2;
        // do reduction if the coefficient is 1 or -1
        if( std::abs(pos2->second) == ScalarType(1) ){
          reducePair(q,pos,pos2);
          goto SearchReduciblePair; // the maps have changed, iterators are no longer valid,
                                    // so do not continue, start again
        }
      }
    }
  }
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
bool ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::removeSimpleHomologyGenerators(
  std::vector<std::vector<P_GeneratorCode> >& simpleHomologyGenerators
){
  bool allRemoved=true;
  int topDim=m_ggb.size()-1;

  simpleHomologyGenerators.clear();
  for(int q=0;q<=topDim;++q){
    simpleHomologyGenerators.push_back(std::vector<GeneratorCode>());
  }

  for(int q=topDim;q>=0;--q){
    for( // every generator in grade q
      typename GeneratorBoundaries::iterator pos = m_ggb[q].begin();
      pos != m_ggb[q].end();
    ){
      const GeneratorCode& gen=pos->first;
      if(
        !pos->second.size() &&         // Boundary is zero
        !m_ggCb[q][gen].size()         // coBoundary is zero
      ){
        simpleHomologyGenerators[q].push_back(pos->first); // add to the vector of removed
        m_ggCb[q].erase(gen);   // remove from the map of coboundaries
        m_ggb[q].erase(pos++);  // remove from the map of boundaries and advance to the next generator
      }else{
        allRemoved=false;
        ++pos;
      }
    }
  }
  return allRemoved;
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
std::ostream& operator<<(std::ostream& out,const ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>& A_rfc){
  int topDim=A_rfc.m_ggb.size()-1;
  out << " *** Reducible Chain Complex *** \n" << std::endl;
  for(int q=topDim;q>=0;--q){
    out << "===========> Dimension " << q << std::endl;
    typedef typename ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::GeneratorBoundaries::const_iterator GeneratorBoundaries_const_iterator;
    for( // every generator in grade q
      GeneratorBoundaries_const_iterator genIt = A_rfc.m_ggb[q].begin();
      genIt != A_rfc.m_ggb[q].end();
      ++genIt
    ){
      out << "  " << genIt->first << " |---> " << genIt->second << std::endl;
    }
  }
  out << " *** End of Reducible Chain Complex *** \n" << std::endl;
  return out;
}

#endif // _REDUCIBLEFREECHAINCOMPLEX_HPP_

/// @}

