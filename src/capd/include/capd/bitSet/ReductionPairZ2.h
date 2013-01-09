/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ReductionPairZ2.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.



// Note: this code is a special version of ReductionPairT,
// which assumes Z2 coefficients and uses bitmaps to store
// chains in order to speed up computations

//   ******* WARNING **********
// As in the case of ReductionPairT this code is for the
// compact sets only!!! This is caused by the use of
// the full boundary map, which in the case of the non-compact
// set should be replaced by the boundary restricted to the current
// set (original set?)

//#include "capd/bitSet/EuclBitSet_BitParIterator.h"
//#include "capd/bitSet/EuclBitSet_BitCoordIterator.h"
#include "capd/repSet/ECellMDCodeT.h"

#if !defined(_REDUCTION_PAIRZ2_H_)
#define _REDUCTION_PAIRZ2_H_

template <typename P_CubeFaceIndex>
class ReductionPairZ2{
public:
  typedef P_CubeFaceIndex CubeFaceIndexType;
  typedef typename CubeFaceIndexType::ClusterType ClusterType;
  typedef ClusterType CubeNumberType;

  template <typename P_Iter>
  ReductionPairZ2(const P_Iter& A_freeIter,const P_Iter& A_companionIter):
    freeFace(A_freeIter.position()),
    companionFace(A_companionIter.position()),
    freeOwnDim(A_freeIter.ownDim()),
    companionOwnDim(A_companionIter.ownDim())
  {}

  template <typename P_Set, typename P_Chain>
  static void reduceAll(const P_Set& A_set,P_Chain& A_chain);

  template <typename P_Set, typename P_Chain>
  static void restoreAll(const P_Set& A_set,P_Chain& A_chain);

  template<typename P_SetChain>
  void reduce(P_SetChain& A_setChain, int chainOwnDim) const;

  template<typename P_SetChain>
  void restore(P_SetChain& A_setChain, int chainOwnDim) const;

private:
  CubeNumberType freeFace;       // the free face or free coface
  CubeNumberType companionFace;  // the index of the unique face (coreduction) or coface (reduction)
  int freeOwnDim;
  int companionOwnDim;
};


// ********** Inline methods definitions ********** //

// This works only for compact sets, needs to be adapted to non-compact case!!!!!!
template <typename P_CubeFaceIndex>
template<typename P_SetChain>
inline void ReductionPairZ2<P_CubeFaceIndex>::reduce(P_SetChain& A_setChain, int chainOwnDim) const{
  static CubeNumberType componentVertex=freeFace;
  /*aaa*/ if(freeOwnDim == 0 and companionOwnDim == 0){       // vertex case
  /*aaa*/   // Warning: do not remove, this is needed! Remember: componentVertex is static!
  /*aaa*/   componentVertex=companionFace;
  /*aaa*/ }else
  if(freeOwnDim<companionOwnDim){  // reduction case: P is free, Q is companion
    const int& k=companionOwnDim;
    const int& l=freeOwnDim;
    if(chainOwnDim==k){
      A_setChain.clearBit(companionFace);  // <c,\dual{Q}>:=0;
    }else{
      if(chainOwnDim==l and A_setChain.getBit(freeFace)){  //  <c,\dual{P}>!=0
        int dim=A_setChain.embDim();
        typename P_SetChain::BitCoordIterator it(A_setChain,companionFace);
        // c+= \bd \dual{Q}
        for(int i=0;i<dim;++i){
          if(it.odd(i)){
            it.incInDir(i);
            it.changeBit();
            it.decInDir(i);
            it.decInDir(i);
            it.changeBit();
            it.incInDir(i);
          }
        }
      }
    }
  }else{ // coreduction case:   Q is free, P is companion
    /*aaa*/ if(chainOwnDim==0){
    /*aaa*/ if(A_setChain.getBit(companionFace)){// coreduction vertex case: if chain is nonzero at P
    /*aaa*/   A_setChain.clearBit(companionFace);
    /*aaa*/   A_setChain.setBit(componentVertex);
    /*aaa*/ }
    /*aaa*/ }else{
      const int& k=freeOwnDim;
      const int& l=companionOwnDim;
      if(chainOwnDim==k) A_setChain.clearBit(freeFace);        // projection
      if(chainOwnDim==l) A_setChain.clearBit(companionFace);   // projection
    /*aaa*/ }
  }
  //-- std::cout << "     After: " << A_setChain  << std::endl; //--
  //-- c-=A_setChain;
  //-- if(!c.isZero()) std::cout << "     Disappeared: " << c  << std::endl; //--
}

// -------------------------------------------------------------------------------------- //

template <typename P_CubeFaceIndex>
template<typename P_SetChain>
inline void ReductionPairZ2<P_CubeFaceIndex>::restore(P_SetChain& A_setChain, int chainOwnDim) const{
  if(freeOwnDim>companionOwnDim and  chainOwnDim==freeOwnDim){  // coreduction case: Q is free, P is companion
    unsigned int scprod=0;
    int dim=A_setChain.embDim();
    typename P_SetChain::BitCoordIterator it(A_setChain,companionFace);
    // c+= \bd \dual{Q}
//cout << "      --- Going through coboundary of: " << it << endl;
    for(int i=0;i<dim;++i){
      if(!it.odd(i)){
        it.incInDir(i);
        if(it.getBit()) scprod^=1U;
//cout << "        --- At: " << it << " scprod is " << scprod << endl;
        it.decInDir(i);
        it.decInDir(i);
        if(it.getBit()) scprod^=1U;
//cout << "        --- At: " << it << " scprod is " << scprod << endl;
        it.incInDir(i);
      }
    }
    if(scprod) A_setChain.changeBit(freeFace);
  }
  // Do nothing in the reduction case (inclusion map)
  return;
}

// -------------------------------------------------------------------------------------- //


template <typename P_CubeFaceIndex>
template <typename P_Set, typename P_Chain>
inline void ReductionPairZ2<P_CubeFaceIndex>::reduceAll(const P_Set& A_set,P_Chain& A_chain){
//cout << "  --- Reducing chain: " << A_chain << endl;
  P_Set setChain(A_set,true);
  setChain.fillWith(A_chain);
  typename std::vector<ReductionPairZ2>::const_iterator it,itEnd;
  it=A_set.getReductors().begin();
  itEnd=A_set.getReductors().end();
  for(;it!=itEnd;++it){
    it->reduce(setChain,A_chain.ownDim());
  }
  P_Chain c;
  c.fillWith(setChain);
  A_chain=c;
//cout << "  --- Reduced chain is: " << A_chain << endl;
}

// -------------------------------------------------------------------------------------- //

template <typename P_CubeFaceIndex>
template <typename P_Set, typename P_Chain>
inline void ReductionPairZ2<P_CubeFaceIndex>::restoreAll(const P_Set& A_set,P_Chain& A_chain){
//cout << "  --- Restoring chain: " << A_chain << endl;
  P_Set setChain(A_set,true);
  setChain.fillWith(A_chain);
  int dim=A_chain.ownDim();
  for(int i=A_set.getReductors().size()-1;i>=0;--i){
    const ReductionPairZ2& rp=A_set.getReductors()[i];
//cout << "    --- Restoring with: " << i << endl;
    rp.restore(setChain,dim);
//cout << "    --- Restored at this stage: " << setChain << endl;
  }
  P_Chain c;
  c.fillWith(setChain);
  A_chain=c;
//cout << "  --- Restored chain is: " << A_chain << endl;
}

/************************************************************************************/

#endif // _REDUCTION_PAIR_H_
/// @}

