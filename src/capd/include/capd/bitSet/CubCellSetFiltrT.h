/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CubCellSetFiltrT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#if !defined(_CUB_CELL_SET_FILTR_H_)
#define _CUB_CELL_SET_FILTR_H_
#include "capd/bitSet/CubCellSetT.h"
#include "capd/bitSet/ReductionPairT.h"
#include "capd/bitSet/ReductionPairZ2.h"
#include <vector>
#include <map>

typedef FreeChainComplex<FreeModule<ElementaryCell,capd::vectalg::Matrix<int,0,0> > > BasicElementaryCellFreeChainComplexType;

template <typename P_Set, typename P_FreeChainComplex=BasicElementaryCellFreeChainComplexType>
class CubCellSetFiltrT{
public:
  typedef P_FreeChainComplex FreeChainComplexType;
  typedef typename P_FreeChainComplex::FreeModuleType FreeModuleType;
  typedef typename FreeModuleType::ScalarType ScalarType;
  typedef ReducibleFreeChainComplex<FreeModuleType> ReducibleFreeChainComplexType;
  typedef typename FreeModuleType::GeneratorType GeneratorType;
  typedef typename P_Set::ReductorType ReductorType;
  typedef ChainT<std::map<GeneratorType,ScalarType> > ChainType;
private:
  // CRefs to the original set and reduced set
//  CRef<P_Set> origSetCR,simplifSetCR;
  CRef<P_Set> simplifSetCR;
  // CRef to ReducibleFreeChainComplex resulting from algebraic reductions performed afer set reductions
  CRef<ReducibleFreeChainComplexType> RFCComplexCR;
  // CRef to QuotientGradedModule remaining after removing simple generators from RFCC
  // This should be changed as soon as the the direct sum operation is available
  CRef<QuotientGradedModule<FreeModuleType> > homologyGradedModuleCR;
  // vector (grade indexed) of vectors of homology base chains
  std::vector<std::vector<ChainType> > baseHomologyChain;
  // vector (grade indexed) of vectors of homology base chains in the simplified form (after reductions)
  std::vector<std::vector<ChainType> > simplifiedBaseHomologyChain;
  // vector (grade indexed) of vectors of orders of homology base chains
  std::vector<std::vector<int> > baseHomologyChainOrder;
  // marker showing if the base chains were restored to their original form
  bool baseChainsRestored;
public:
  CubCellSetFiltrT(CRef<P_Set> A_setCR,bool A_restoreBaseChains=true);

  bool BaseChainsRestored() const{
    return baseChainsRestored;
  }

/*
  CRef<P_Set> getOrigSetCR() const{
    return origSetCR;
  }
*/
  // The following change is intended to get read of origSetCR, which seems to only waste memory
  CRef<P_Set> getSetCR() const{
    return simplifSetCR;
  }

  const QuotientGradedModule<FreeModuleType>& filteredHomModule() const{
    return homologyGradedModuleCR();
  }

  const std::vector<std::vector<ChainType> >& BaseHomologyChain() const{
    return baseHomologyChain;
  }

  const std::vector<std::vector<ChainType> >& SimplifiedBaseHomologyChain() const{
    return simplifiedBaseHomologyChain;
  }

  int TopDim(){
    return baseHomologyChain.size()-1;
  }

  // This works only for compact sets, needs to be adapted to non-compact case.
  template<typename P_Chain>
  void reduce(P_Chain& A_chain) const;

  template<typename P_Chain>
  void restore(P_Chain& A_chain) const;

  int bettiNumber(int q) const{
    int b=0;
    if(homologyGradedModuleCR().TopDim()>=q){
      b=homologyGradedModuleCR().component(q).rank();  // generators from Smith computation
    }
    if(int(baseHomologyChain.size())>q){
      b+=baseHomologyChain[q].size();                  // generators from algebraic reductions
    }
    return b;
  }

  int maxCycleSize(int q);
  void cycleSizeSpectrum(int q,std::map<int,int>& A_spect);

  const std::vector<ReductorType>& getReductors() const{
    return simplifSetCR().getReductors();
  }

  friend std::ostream& operator<<(std::ostream& out, const CubCellSetFiltrT& A_filtr){
    out << " --- Filtration of a cubical set with the homology generators --- \n\n";
    for(unsigned int q=0;q<A_filtr.baseHomologyChain.size();++q){
      out << "  Dimension " << q << "\n";
      for(unsigned int j=0;j<A_filtr.baseHomologyChain[q].size();++j){
        out << "    Base chain " << j << " of order " << A_filtr.baseHomologyChainOrder[q][j] << "\n";
//        out << "    original: " << A_filtr.baseHomologyChain[q][j] << "\n";
        out << "    simplified: " << A_filtr.simplifiedBaseHomologyChain[q][j] << "\n";
      }
    }
    return out;
  }

};

// -------------------------------------------------------------------------------------- //

// ********** Inline methods definitions ********** //

/************************************************************************************/

#endif // _CUB_CELL_SET_FILTR_H_
/// @}

