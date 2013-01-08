/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ReductionPairT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.



// Note: this code is less general than the code in the internal class ReducibleFreeChainComplex::ReducedPair,
// but it is faster. Both, ReductionPairT and ReducedPair are needed



#if !defined(_REDUCTION_PAIR_H_)
#define _REDUCTION_PAIR_H_

template <typename P_CubeFaceIndex>
class ReductionPairT{
//private:
public:
  P_CubeFaceIndex freeCubeIndex;       // the index of the free face or free coface
  P_CubeFaceIndex companionCubeIndex;  // the index of the unique face (coreduction) or coface (reduction)
public:
  typedef P_CubeFaceIndex CubeFaceIndexType;
  ReductionPairT(const CubeFaceIndexType& A_freeCFI,const CubeFaceIndexType& A_companionCFI):
    freeCubeIndex(A_freeCFI),companionCubeIndex(A_companionCFI){
  }
  template<typename P_Iter>
  ReductionPairT(const P_Iter& A_freeBCI,const P_Iter& A_companionBCI):
    freeCubeIndex(A_freeBCI),companionCubeIndex(A_companionBCI){}

  template <typename P_EuclSet, typename P_Chain>
  static void reduceAll(const P_EuclSet& A_set,P_Chain& A_chain);

  template <typename P_EuclSet, typename P_Chain>
  static void restoreAll(const P_EuclSet& A_set,P_Chain& A_chain);


  template<typename P_Chain, typename P_Set>
  void reduceInDimZero(P_Chain& A_chain,P_Set& A_set) const;


  template<typename P_Chain, typename P_Set>
  void reduce(P_Chain& A_chain, P_Set& A_set) const;

  template<typename P_Chain, typename P_Set>
  void restore(P_Chain& A_chain, P_Set& A_set) const;
};


// ********** Inline methods definitions ********** //

// This works only for compact sets, needs to be adapted to non-compact case.
// There reason is that we take full boundary when computing modifying chain
// The boundary must be taken in the set at the respective moment of the reduction
// In the compact case the boundary is always the full boundary,

template <typename P_CubeFaceIndex>
template<typename P_Chain, typename P_Set>
inline void ReductionPairT<P_CubeFaceIndex>::reduce(P_Chain& A_chain, P_Set& A_set) const{
  typedef typename P_Chain::GeneratorCodeType GeneratorType;
  typedef typename P_Chain::ScalarType ScalarType;
  GeneratorType freeFace(A_set,freeCubeIndex);                    // P
  GeneratorType companionFace(A_set,companionCubeIndex);          // Q
  //-- fcout << " Reducing through pair (" << freeFace << "," << companionFace << ")\n"; //--
  //-- std::cout << "    Before: " << A_chain  << std::endl; //--
/* Only needed in the reduction case when the reduced set is noncompact (not used so far)
  freeFace.clearBit();
  companionFace.clearBit();
*/
  /*aaa*/ static GeneratorType componentVertex=freeFace;
  int freeOwnDim=freeFace.ownDim();
  int companionOwnDim=companionFace.ownDim();
  int chainOwnDim=A_chain.ownDim();
  /*aaa*/ if(freeOwnDim == 0 and companionOwnDim == 0){       // vertex case
  /*aaa*/   // Warning: do not remove, this is needed! Remember: componentVertex is static!
  /*aaa*/   componentVertex=companionFace;
  /*aaa*/ }else
  if(freeOwnDim<companionOwnDim){               // reduction case: P is free, Q is companion
    int& k=companionOwnDim;
    int& l=freeOwnDim;
    if(chainOwnDim==k) A_chain.erase(companionFace);  // <c,\dual{Q}>:=0;
    ScalarType chainAtFreeFace;
    if(chainOwnDim==l and (chainAtFreeFace=A_chain.at(freeFace)) != ScalarType(0)){
      P_Chain modifyingChain;
      // ***** This is the line which is delicate!!!
      // ***** Works when reductions are applied to a compact set!!!
      // ***** Otherwise will get wrong answers!!!!
      companionFace.boundary(modifyingChain);                       // \bd \dual{Q} in modifyingChain
      ScalarType s=-chainAtFreeFace*modifyingChain.at(freeFace);    // s= - <c,\dual{P}><\bd \dual{Q},\dual{P}>
      modifyingChain*=s;
      //-- std::cout << "     modifyingChain: " << modifyingChain  << std::endl; //--
      A_chain+=modifyingChain;                                      // c+= s* \bd \dual{Q}
      A_chain.erase(freeFace);                                      // now chain c is zero at P (the above should imply this?)
    }
  }else{    // coreduction case:  Q is free, P is companion
    /*aaa*/ if(chainOwnDim==0){
    /*aaa*/ if(A_chain.find(companionFace)!=A_chain.end()){// coreduction vertex case: Q is free, P is companion
    /*aaa*/   P_Chain c;
    /*aaa*/   c.insert(make_pair(componentVertex,ScalarType(1)));
    /*aaa*/   A_chain=c;
    /*aaa*/ }
    /*aaa*/ }else{
      int& k=freeOwnDim;
      int& l=companionOwnDim;
      if(chainOwnDim==k) A_chain.erase(freeFace);        // projection
      if(chainOwnDim==l) A_chain.erase(companionFace);   // projection
    /*aaa*/ }
  }
  //-- std::cout << "     After: " << A_chain  << std::endl; //--
  //-- if(!c.isZero()) std::cout << "     Disappeared: " << c  << std::endl; //--
}


// -------------------------------------------------------------------------------------- //

// This is the hopefully obsolete special version for chains in dim zero
// Since most of this code coincides with the nonzero case, I incorporated this code
// in the code for the nonzero version above. Changes are marked with /*aaa*/
template <typename P_CubeFaceIndex>
template<typename P_Chain, typename P_Set>
inline void ReductionPairT<P_CubeFaceIndex>::reduceInDimZero(P_Chain& A_chain,P_Set& A_set) const{
  typedef typename P_Chain::GeneratorCodeType GeneratorType;
  typedef typename P_Chain::ScalarType ScalarType;
  GeneratorType freeFace(A_set,freeCubeIndex);                    // P
  GeneratorType companionFace(A_set,companionCubeIndex);          // Q
  static GeneratorType componentVertex=freeFace;
//--fcout << " Reducing through pair (" << freeFace << "," << companionFace << ")\n"; //--
//--P_Chain c(A_chain);   //--
      //-- std::cout << "    Before: " << A_chain  << std::endl; //--
/* Only needed in the reduction case when the reduced set is noncompact (not used so far)
  freeFace.clearBit();
  companionFace.clearBit();
*/
  int freeOwnDim=freeFace.ownDim();
  int companionOwnDim=companionFace.ownDim();
  if(freeOwnDim > 0 and companionOwnDim > 0) return;
  if(freeOwnDim == 0 and companionOwnDim == 0){       // vertex case
    // Warning: do not remove, this is needed! Remember: componentVertex is static!
    componentVertex=companionFace;
  }else if(freeOwnDim<companionOwnDim){               // reduction case: P is free, Q is companion
    ScalarType chainAtFreeFace;
    if((chainAtFreeFace=A_chain.at(freeFace)) != ScalarType(0)){
      P_Chain modifyingChain;
      // ***** This is the line which is delicate!!!
      // ***** Works when reductions are applied to a compact set!!!
      // ***** Otherwise will get wrong answers!!!!
      companionFace.boundary(modifyingChain);                       // \bd \dual{Q} in modifyingChain
/*    inefficient coding, replaced by better coding below
      modifyingChain=-modifyingChain.at(freeFace)*modifyingChain;   // - <\bd \dual{Q},\dual{P}> \bd \dual{Q}
      modifyingChain.erase(freeFace);                               // \dual{P} - <\bd \dual{Q},\dual{P}> \bd \dual{Q}
                                                                    // (the above chain is zero at P)
      A_chain+=chainAtFreeFace*modifyingChain;
*/
      ScalarType s=-chainAtFreeFace*modifyingChain.at(freeFace);    // s= - <c,\dual{P}><\bd \dual{Q},\dual{P}>
      modifyingChain*=s;
      //-- std::cout << "     modifyingChain: " << modifyingChain  << std::endl; //--
      A_chain+=modifyingChain;                                      // c+= s* \bd \dual{Q}
    }
  }else if(A_chain.find(companionFace)!=A_chain.end()){// coreduction vertex case: Q is free, P is companion
    P_Chain c;
    c.insert(make_pair(componentVertex,ScalarType(1)));
    A_chain=c;
  }
  //-- std::cout << "     After: " << A_chain  << std::endl; //--
  //-- c-=A_chain;
  //-- if(!c.isZero()) std::cout << "     Disappeared: " << c  << std::endl; //--
}

// -------------------------------------------------------------------------------------- //

template <typename P_CubeFaceIndex>
template<typename P_Chain, typename P_Set>
inline void ReductionPairT<P_CubeFaceIndex>::restore(P_Chain& A_chain, P_Set& A_set) const{
  typedef typename P_Chain::GeneratorCodeType GeneratorType;
  typedef typename P_Chain::ScalarType ScalarType;
  GeneratorType freeFace(A_set,freeCubeIndex);
  GeneratorType companionFace(A_set,companionCubeIndex);
      //-- fcout << " Restoring through pair (" << freeFace << "," << companionFace << ")\n"; //--
      //-- P_Chain c(A_chain);   //--
      //-- std::cout << "    Before: " << A_chain  << std::endl; //--
  int k;
  if((k=freeFace.ownDim())>companionFace.ownDim() and A_chain.ownDim()==k){  // coreduction case
    P_Chain modifyingChain;
    // Taking here full coboundary is ok, because c at every stage the support of c is contained in the respective set,
    // so the elements of \cbdy P outside the set do not matter.
    companionFace.coBoundary(modifyingChain);                                // \cbd \dual{P}

    ScalarType coef=-(modifyingChain*A_chain);  // coef=-<\cbd\dual{P},c>
    if(!coef) return;
    coef*=modifyingChain.at(freeFace);                 // coef*=<\bd\dual{Q},\dual{P}> lub coef*=\cbd\dual{P}(\dual{Q})
    //-- std::cout << "     modifyingChain: " << modifyingChain  << std::endl; //--
    if(coef) A_chain.insert(make_pair(freeFace,coef)); // c(Q)=coef;
    //-- std::cout << "     After: " << A_chain  << std::endl; //--
  }
  // Do nothing in the reduction case (inclusion map)
  return;
}

// -------------------------------------------------------------------------------------- //

template <typename P_CubeFaceIndex>
template <typename P_EuclSet, typename P_Chain>
inline void ReductionPairT<P_CubeFaceIndex>::reduceAll(const P_EuclSet& A_set,P_Chain& A_chain){
//cout << "  --- Reducing chain: " << A_chain << endl;
  typename std::vector<ReductionPairT>::const_iterator it,itEnd;
  it=A_set.getReductors().begin();
  itEnd=A_set.getReductors().end();
  for(;it!=itEnd;++it){
//std::cout << " reducing " << A_chain << std::endl;
    it->reduce(A_chain,A_set);
  }
//cout << "  --- Reduced chain is: " << A_chain << endl;
}

// -------------------------------------------------------------------------------------- //

template <typename P_CubeFaceIndex>
template <typename P_EuclSet, typename P_Chain>
inline void ReductionPairT<P_CubeFaceIndex>::restoreAll(const P_EuclSet& A_set,P_Chain& A_chain){
//cout << "  --- Restoring chain: " << A_chain << endl;
  for(int i=A_set.getReductors().size()-1;i>=0;--i){
    A_set.getReductors()[i].restore(A_chain,A_set);
  }
//cout << "  --- Restored chain is: " << A_chain << endl;
}

/************************************************************************************/

#endif // _REDUCTION_PAIR_H_
/// @}

