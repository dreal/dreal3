/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file homAlgFunctors.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_ALGFUNCT_H_)
#define _ALGFUNCT_H_

#include <time.h>
#include "capd/homologicalAlgebra/FreeModule.h"
#include "capd/homologicalAlgebra/HomologySignature.h"
#include "capd/homologicalAlgebra/FreeChainComplex.h"
#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.h"
#include "capd/homologicalAlgebra/QuotientGradedModule.h"
#include "capd/auxil/CRef.h"
#include "capd/auxil/Functor.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/auxil/ofstreamcout.h"

extern ofstreamcout fcout;

// -------------------------------------------------------------------------------------- //



// -------------------------------------------------------------------------------------- //

template<typename P_FreeModule>
class HomAlgFunctors{

  public:

  typedef P_FreeModule FreeModuleType;
  typedef typename FreeModuleType::MatrixType::ScalarType ScalarType;
  typedef HomologySignature<ScalarType> HomologySignatureType;
  typedef ReducibleFreeChainComplex<FreeModuleType> ReducibleFreeChainComplexType;
  typedef FreeChainComplex<FreeModuleType> FCComplex;
  typedef Functor<CRef<HomologySignatureType>,CRef<ReducibleFreeChainComplexType> > HomSign_RFCComplex;
  typedef Functor<CRef<QuotientGradedModule<FreeModuleType> >,CRef<FCComplex> > Homology_FCComplex;

  // -------------------------------------------------------------------------------------- //

  static CRef<QuotientGradedModule<FreeModuleType> > HomologyViaSmith(
   CRef<FreeChainComplex<FreeModuleType> > A_fccCR
  ){
    typedef typename FreeModuleType::MatrixType MatrixType;
    typedef typename FreeModuleType::GeneratorType GeneratorType;
    int topDim=A_fccCR().topDim();
    if(topDim<0){
      CRef<QuotientGradedModule<FreeModuleType> > homologyGradedModuleCR(
        new QuotientGradedModule<FreeModuleType>()
      );
      return homologyGradedModuleCR;
    }
    std::vector<MatrixType> cycles(topDim+1);
    std::vector<MatrixType> boundaries(topDim+1);
    // We begin with computing the cycles and boundaries from the boundary map
    // for dimension from topDim to 1
    for(int i=topDim;i>0;--i){
      MatrixType m(A_fccCR().boundaryHomomorphism(i).coefMatrix());
      capd::matrixAlgorithms::kernelImage(
        m,
        cycles[i],
        boundaries[i-1]
      );
    }
    // The above procedures misses cycles in dimension zero and boundaries in dimension topDim
    // Boundaries in dimension topDim are zero anyway but we neeed to add cycles in dimension zero
    cycles[0]=MatrixType::Identity(A_fccCR().chainModule(0).numberOfGenerators());
    boundaries[topDim]=MatrixType(A_fccCR().chainModule(topDim).numberOfGenerators(),0);

    std::vector<QuotientModule<FreeModuleType> > quotientModuleVector(topDim+1);
    for(int i=0;i<topDim+1;++i){
      QuotientModule<FreeModuleType> qM(
        A_fccCR().chainModule(i),
        cycles[i],
        boundaries[i]
      );

      swap(quotientModuleVector[i],qM);
    }
    CRef<QuotientGradedModule<FreeModuleType> > homologyGradedModuleCR(
      new QuotientGradedModule<FreeModuleType>(quotientModuleVector,A_fccCR)
    );
    return homologyGradedModuleCR;
  }  // ********** Homology FreeChainComplex<FreeModuleType> ********** //

  static Homology_FCComplex homology_Smith_FCComplex;

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> homSignViaSmith(
   CRef<FreeChainComplex<FreeModuleType> > A_fccCR
  ){
   typedef typename FreeModuleType::MatrixType MatrixType;
   typedef typename FreeModuleType::GeneratorType GeneratorType;
   int topDim=A_fccCR().topDim();
   if(topDim<0) return CRef<HomologySignatureType>(new HomologySignatureType());
   std::vector<MatrixType> cycles(topDim+1);
   std::vector<MatrixType> boundaries(topDim+1);
   // We begin with computing the cycles and boundaries from the boundary map
   // for dimension from topDim to 1
   for(int i=topDim;i>0;--i){
     MatrixType m(A_fccCR().boundaryHomomorphism(i).coefMatrix());
     capd::matrixAlgorithms::kernelImage(
       m,
       cycles[i],
       boundaries[i-1]
     );
   }
   // The above procedure misses cycles in dimension zero and boundaries in dimension topDim
   // Boundaries in dimension topDim are zero anyway but we neeed to add cycles in dimension zero
   cycles[0]=MatrixType::Identity(A_fccCR().chainModule(0).numberOfGenerators());
   boundaries[topDim]=MatrixType(A_fccCR().chainModule(topDim).numberOfGenerators(),0);

   std::vector<QuotientModule<FreeModuleType> > quotientModuleVector(topDim+1);
   for(int i=0;i<topDim+1;++i){
     QuotientModule<FreeModuleType> qM(
       A_fccCR().chainModule(i),
       cycles[i],
       boundaries[i]
     );

     swap(quotientModuleVector[i],qM);
   }

   QuotientGradedModule<FreeModuleType> homologyGradedModule(quotientModuleVector,A_fccCR);
   return CRef<HomologySignatureType>(homologyGradedModule); // the use of CRef seems to be incorrect 23.08.2006
  }

  static typename ReducibleFreeChainComplexType::ReducibleFreeChainComplex_void_Ptr reduce;  // Is this what I wanted? 23.08.2006

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> homSignViaAR(
   CRef<ReducibleFreeChainComplexType> A_rfccCR
  ){

    typedef typename FreeModuleType::MatrixType MatrixType;
    typedef typename FreeModuleType::GeneratorType GeneratorType;

    CRef<HomologySignatureType> homSignCR(new HomologySignatureType());
    CRef<HomologySignatureType> homSignSmithCR(new HomologySignatureType());
    Stopwatch t;
    int pairsReduced=(A_rfccCR().*reduce)();
    fcout << "Algebraic reductions (KMS) of " << pairsReduced << " pairs in " << t << std::endl;

    // We first check if the reductions were total, i.e. if all generators are now in the kernel
    // of the boundary operator
    // If so, there is no need to apply Smith, which may take time
    // Otherwise we apply Smith.
    // However this is a temporary solution: in every case we should apply Smith to the complex remaining
    // after the removal of all kernel generators and then take the direct sum of the Smith outcome and the removed generators
    // -- MMStopwatch t2;
    std::vector<std::vector<typename ReducibleFreeChainComplexType::GeneratorCode> > simpleHomologyGenerators;
    bool fullyReduced=A_rfccCR().removeSimpleHomologyGenerators(simpleHomologyGenerators);
    // -- MM  fcout << "Simple homology generators removed in " << t2 << std::endl;

    // -- MM  Stopwatch t3;
    // First prepare the part of homology signature based on simple homology generators
    for(unsigned int i=0;i<simpleHomologyGenerators.size();++i){
     int betti=simpleHomologyGenerators[i].size();
     // There are no torsion coefficients, so put only Betti numbers
     std::vector<int> empty;
     homSignCR().push_back( FGAGrpSignature<ScalarType> (betti,empty ) );
    }
    // -- MM  fcout << "Simple Betti numbers computed in " << t3 << std::endl;

    // Now find the other generators, in particular torsion generators
    if(!fullyReduced){
      Stopwatch s;
      CRef<FreeChainComplex<FreeModuleType> > fccCR(new FreeChainComplex<FreeModuleType>(A_rfccCR()));
      homSignSmithCR=homSignViaSmith(fccCR);
      fcout << "Homology of " << fccCR().numberOfGenerators() << " generators via Smith diagonalization in " << s  << std::endl;
    }else{
      fcout << "Fully reduced, Smith diagonalization not needed " << std::endl;
    }
    // -- MM  Stopwatch t4;
    homSignCR()+=homSignSmithCR();
    homSignCR().shrink();
    // -- MM  fcout << "Total signature computed in " << t4 << std::endl;

    return homSignCR;
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> homSignViaAR_Random(
   CRef<ReducibleFreeChainComplexType> A_rfccCR
  ){
    reduce=&ReducibleFreeChainComplexType::reduce;
    return homSignViaAR(A_rfccCR);
  }

  static HomSign_RFCComplex homSign_ArRandom_RFCComplex;

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> homSignViaAR_Sorted(
   CRef<ReducibleFreeChainComplexType> A_rfccCR
  ){
    reduce=&ReducibleFreeChainComplexType::reduceViaSort;
    return homSignViaAR(A_rfccCR);
  }

  static HomSign_RFCComplex homSign_ArSorted_RFCComplex;

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> homSignViaAR_LocallySorted(
   CRef<ReducibleFreeChainComplexType> A_rfccCR
  ){
    reduce=&ReducibleFreeChainComplexType::reduceViaLocalSort;
    return homSignViaAR(A_rfccCR);
  }

  static HomSign_RFCComplex homSign_ArLocallySorted_RFCComplex;

  // -------------------------------------------------------------------------------------- //

};// class HomAlgFunctors

template<typename FreeModuleType>
typename HomAlgFunctors<FreeModuleType>::Homology_FCComplex HomAlgFunctors<FreeModuleType>::homology_Smith_FCComplex(&HomAlgFunctors::HomologyViaSmith);

template<typename FreeModuleType>
typename HomAlgFunctors<FreeModuleType>::ReducibleFreeChainComplexType::ReducibleFreeChainComplex_void_Ptr HomAlgFunctors<FreeModuleType>::reduce(&HomAlgFunctors<FreeModuleType>::ReducibleFreeChainComplexType::reduce);

template<typename FreeModuleType>
typename HomAlgFunctors<FreeModuleType>::HomSign_RFCComplex HomAlgFunctors<FreeModuleType>::homSign_ArRandom_RFCComplex(&HomAlgFunctors::homSignViaAR_Random);

template<typename FreeModuleType>
typename HomAlgFunctors<FreeModuleType>::HomSign_RFCComplex HomAlgFunctors<FreeModuleType>::homSign_ArSorted_RFCComplex(&HomAlgFunctors::homSignViaAR_Sorted);

template<typename FreeModuleType>
typename HomAlgFunctors<FreeModuleType>::HomSign_RFCComplex HomAlgFunctors<FreeModuleType>::homSign_ArLocallySorted_RFCComplex(&HomAlgFunctors::homSignViaAR_LocallySorted);

// Here various flavours for testing
// HomAlgFunctors<ZFreeModule>::HomSign_RFCComplex& homSign_ArRandom_ZRFCComplex=HomAlgFunctors<ZFreeModule>::homSign_ArRandom_RFCComplex;
// HomAlgFunctors<ZFreeModule>::HomSign_RFCComplex& homSign_ArSorted_ZRFCComplex=HomAlgFunctors<ZFreeModule>::homSign_ArSorted_RFCComplex;
//HomAlgFunctors<ZFreeModule>::HomSign_RFCComplex& homSign_ArLocallySorted_ZRFCComplex=HomAlgFunctors<ZFreeModule>::homSign_ArLocallySorted_RFCComplex;
// and homSign_AR_ZRFCComplex is for the general use selected as the most likely best
// HomAlgFunctors<ZFreeModule>::HomSign_RFCComplex& homSign_AR_ZRFCComplex=HomAlgFunctors<ZFreeModule>::homSign_ArRandom_RFCComplex;

// -------------------------------------------------------------------------------------- //
#endif //_ALGFUNCT_H_
/// @}

