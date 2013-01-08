/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CubCellSetFiltrT.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#if !defined(_CUB_CELL_SET_FILTR_HPP_)
#define _CUB_CELL_SET_FILTR_HPP_
#include <typeinfo>
#include "capd/bitSet/CubCellSetFiltrT.h"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"

// -------------------------------------------------------------------------------------- //
template <typename P_Set,typename P_FreeChainComplex>
CubCellSetFiltrT<P_Set,P_FreeChainComplex>::CubCellSetFiltrT(CRef<P_Set> A_setCR,bool A_restoreBaseChains):
  homologyGradedModuleCR(new QuotientGradedModule<FreeModuleType>()),
  baseChainsRestored(false)
{
  A_setCR().addEmptyCollar();
//  origSetCR=CRef<P_Set>(new P_Set(A_setCR()));  // Not used and wasting memory? Seems to be used only in InclusionHomology
                                                  // for testing the sizes and this can be done through the reduced set
  // perform the reduction and store the reduction pairs
//  simplifSetCR=CubSetFunctors<BCubSet,P_Set,P_FreeChainComplex>::CubCelSet_CR_CubCelSet(A_setCR);
  simplifSetCR=CubSetFunctors<BCubSet,P_Set,P_FreeChainComplex>::CubCelSetReduce(A_setCR); // the above doesn't compile under gcc336 on Linux
  // construct the reducible free chain complex with the option of storing the reductions.
  // -- fcout << "   The set after reduction is:\n";
  // -- fcout << simplifSetCR() << std::endl;
  const bool storeReduciblePairs=true;
  RFCComplexCR=CRef<ReducibleFreeChainComplexType>(new ReducibleFreeChainComplexType(simplifSetCR(),storeReduciblePairs));

  Stopwatch t;
  int pairsReduced=(RFCComplexCR().reduce)();
  fcout << "Algebraic reductions (KMS) of " << pairsReduced << " pairs in " << t << std::endl;
  // -- fcout << "Reducible free chain complex after reductions is: \n" << RFCComplexCR() << std:: endl; // -- MM

  // remove simple homology generators and add the respective base chains to baseHomologyChain
  std::vector<std::vector<typename ReducibleFreeChainComplexType::GeneratorCode> > simpleHomologyGenerators;
  bool fullyReduced=RFCComplexCR().removeSimpleHomologyGenerators(simpleHomologyGenerators);
  int topDimSimple=simpleHomologyGenerators.size()-1;
  int topDimFromSmith=0;

  if(!fullyReduced){
    // find the homology of the reduced set
    CRef<FreeChainComplexType> FCComplexCR(new FreeChainComplexType(RFCComplexCR()));
    Stopwatch smithWatch;
//    homologyGradedModuleCR=HomAlgFunctors<FreeModuleType>::homology_Smith_FCComplex(FCComplexCR);
    homologyGradedModuleCR=HomAlgFunctors<FreeModuleType>::HomologyViaSmith(FCComplexCR); // the above doesn't compile under gcc336 on Linux
    std::cout << "Smith took " << smithWatch << std::endl;
    topDimFromSmith=homologyGradedModuleCR().TopDim();
  }
  int topDim=std::max(topDimSimple,topDimFromSmith);

  // prepare topDim empty vectors for homology generators in every dimension
  for(int i=0;i<=topDim;++i){  // for every homology dimension
    baseHomologyChain.push_back(std::vector<ChainType>());
    simplifiedBaseHomologyChain.push_back(std::vector<ChainType>());
    baseHomologyChainOrder.push_back(std::vector<int>());
  }

  // Store the homology generators
  for(int q=0;q<=topDim;++q){  // for every homology dimension
    // We first store the generators obtained from Smith
    if(q<topDimFromSmith){
      // This code should be optimized, note that the chains in baseHomologyChain[q]
      // are brought to its final form in the next for loop!!
      homologyGradedModuleCR().component(q).exportBaseChains(baseHomologyChain[q],baseHomologyChainOrder[q]);
      homologyGradedModuleCR().component(q).exportBaseChains(simplifiedBaseHomologyChain[q],baseHomologyChainOrder[q]);
    }
    // and now we store the simple generators note that the chains in baseHomologyChain[q]
    // are brought to its final form in the next for loop!!
    if(q<topDimSimple){
      for(unsigned int j=0;j<simpleHomologyGenerators[q].size();++j){
      // This code should be optimized
        baseHomologyChain[q].push_back(ChainType(simpleHomologyGenerators[q][j]));
        simplifiedBaseHomologyChain[q].push_back(ChainType(simpleHomologyGenerators[q][j]));
        baseHomologyChainOrder[q].push_back(0);
      }
    }
  }

  // Now restore the base generators in baseHomologyChain[q] to their form in the set before reduction
  if(A_restoreBaseChains){
    Stopwatch restoringWatch;
    for(int q=0;q<=topDim;++q){  // for every homology dimension
      Stopwatch restoringWatchForOneDim;
//int cnt=0;
      for( // for every generator in grade dimension q
        typename std::vector<ChainType>::iterator it=baseHomologyChain[q].begin();
        it != baseHomologyChain[q].end();
        ++it
      ){
        restore(*it);
//++cnt;
      }
/*
      fcout << "   >>> Restored " << cnt << " chains in " << restoringWatchForOneDim.worldTime()/cnt << " sec per chain" << std::endl;
      fcout << "   >>> Restoring in dim " << q << " took " << restoringWatchForOneDim << std::endl;
*/
    }
    std::cout << "Restoring took " << restoringWatch << std::endl;
    baseChainsRestored=true;
  }
}

// -------------------------------------------------------------------------------------- //

template <typename P_Set,typename P_FreeChainComplex>
int CubCellSetFiltrT<P_Set,P_FreeChainComplex>::maxCycleSize(int q){
  unsigned int maxSize=0;
  for(unsigned int i=0;i<baseHomologyChain[q].size();++i){
    maxSize=std::max(baseHomologyChain[q][i].size(),maxSize);
  }
  return (int)maxSize;
}

// -------------------------------------------------------------------------------------- //

template <typename P_Set,typename P_FreeChainComplex>
void CubCellSetFiltrT<P_Set,P_FreeChainComplex>::cycleSizeSpectrum(int q,std::map<int,int>& A_spect){
  for(unsigned int i=0;i<baseHomologyChain[q].size();++i){
    int size=baseHomologyChain[q][i].size();
    if(A_spect.find(size)==A_spect.end()) A_spect[size]=1;
    else ++A_spect[size];
  }
}

// This works only for compact sets, needs to be adapted to non-compact case.
// -------------------------------------------------------------------------------------- //
template <typename P_Set,typename P_FreeChainComplex>
template<typename P_Chain>
void CubCellSetFiltrT<P_Set,P_FreeChainComplex>::reduce(P_Chain& A_chain) const{
  // First do the reducing through the elementary (cubical) reduction pairs
  ReductorType::reduceAll(simplifSetCR(),A_chain);
  // And then do the reducing through the algebraic reduction pairs
  RFCComplexCR().reduce(A_chain);
}

// -------------------------------------------------------------------------------------- //
template <typename P_Set,typename P_FreeChainComplex>
template<typename P_Chain>
void CubCellSetFiltrT<P_Set,P_FreeChainComplex>::restore(P_Chain& A_chain) const{
  // First do the restoring through the algebraic reduction pairs
  RFCComplexCR().restore(A_chain);
  int chainOwnDim=A_chain.ownDim();
  if(chainOwnDim == 0) return;

  // And then do the restoring through the elementary (cubical) reduction pairs
  ReductorType::restoreAll(simplifSetCR(),A_chain);

}

/************************************************************************************/

#endif // _CUB_CELL_SET_FILTR_HPP_
/// @}

