/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file cubSetFunctors.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_CUBFUNCT_H_)
#define _CUBFUNCT_H_

#include <time.h>
#include <set>
#include "capd/homologicalAlgebra/HomologySignature.h"
#include "capd/homologicalAlgebra/homAlgFunctors.hpp"
#include "capd/auxil/CRef.h"
#include "capd/auxil/Functor.h"
#include "capd/auxil/Stopwatch.h"
#include "capd/repSet/ElementaryCell.h"
#include "capd/repSet/ElementaryCube.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"
#include "capd/auxil/memSize.h"

using capd::matrixAlgorithms::kernelImage;
using capd::matrixAlgorithms::quotientBaseMatrix;

typedef FreeChainComplex<FreeModule<ElementaryCell,capd::vectalg::Matrix<int,0,0> > > BasicElementaryCellFreeChainComplexType;

// -------------------------------------------------------------------------------------- //
/*
  Class template CubSetFunctors is actually only a container for
  the definitions of functors (functions represented as objects)
  for various transformations of cubical sets.
  The template parameters P_CubSet and P_CubCelSet are assumed to be classes
  representing full cubical sets and cellural cubical sets (representable cubical sets)
  respectively. All the functors are static objects of the class associated
  to respective static functions defined in the class. The association is done
  via definition templates just after the definition of the class
*/
// -------------------------------------------------------------------------------------- //
//int lastAcyclicSubsetSize=0;

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex=BasicElementaryCellFreeChainComplexType>
class CubSetFunctors{

  public:



  // Shorthands for various types of CubSet Functors
  typedef P_FreeChainComplex FreeChainComplexType;
  typedef typename FreeChainComplexType::FreeModuleType FreeModuleType;
  typedef typename FreeModuleType::GeneratorType GeneratorType;
  typedef typename FreeModuleType::ScalarType ScalarType;
  typedef HomologySignature<ScalarType> HomologySignatureType;

  // Define the free module with generators of type int
  // (needed when original generators (like ElementaryCell) are memory inefficient and require coding in a word
  // in reducible free chain complex reductions. The new ECellMDCode eliminates the need of ZGenFreeModule
  // but still some executables unnecessarily use inefficient ElementaryCell
  typedef FreeModule<int,capd::vectalg::Matrix<ScalarType,0,0> > ZGenFreeModule;
  // Define the reducible free chain complex with consecutive generators encoded as consecutive integers,
  // so that ZGenFreeModule may be used (encoding is provided by the class)
  typedef ReducibleFreeChainComplex<ZGenFreeModule,int> ZGenRFCComplex;

  typedef ReducibleFreeChainComplex<FreeModuleType,GeneratorType> ReducibleFreeChainComplexType;

  typedef Functor<CRef<ZGenRFCComplex>,CRef<P_CubCelSet> > RFCComplexOverZ_CubCelSet_FunctorType;
  typedef Functor<CRef<ZGenRFCComplex>,CRef<P_CubSet> > RFCComplexOverZ_CubSet_FunctorType;

  typedef Functor<CRef<ReducibleFreeChainComplexType>,CRef<P_CubCelSet> > RFCComplex_CubCelSet_FunctorType;
  typedef Functor<CRef<ReducibleFreeChainComplexType>,CRef<P_CubSet> > RFCComplex_CubSet_FunctorType;
  typedef Functor<CRef<P_CubSet>,CRef<P_CubSet> > CubSet_CubSet_FunctorType;
  typedef Functor<CRef<P_CubCelSet>,CRef<P_CubSet> > CubCelSet_CubSet_FunctorType;
  typedef Functor<CRef<P_CubCelSet>,CRef<P_CubCelSet> > CubCelSet_CubCelSet_FunctorType;

  typedef typename P_CubSet::BoolBCI_Ptr BoolBCI_Ptr;
  typedef typename P_CubSet::BoolBI_Ptr BoolBI_Ptr;

  typedef typename P_CubSet::CubSetT_void_Ptr CubSetT_void_Ptr;
  typedef typename P_CubSet::CubSetT_CubSetT_Ptr CubSetT_CubSetT_Ptr;

  typedef Functor<CRef<FreeChainComplexType>,CRef<P_CubCelSet> > FreeChainComplex_CubCelSet_FunctorType;

  static CubSetT_void_Ptr shave;
  static CubSetT_CubSetT_Ptr acyclicSubspace;

  // Define the free module with generators of type int
//  typedef FreeModule<int,capd::vectalg::Matrix<int,0,0> > ZGenFreeModule;




  static int lastAcyclicSubsetSize;

  // -------------------------------------------------------------------------------------- //

  static CRef<P_CubCelSet> BCubCelSetFromBCubSet(CRef<P_CubSet> A_cubSetCR){
    Stopwatch swCollar;
    A_cubSetCR().addEmptyCollar();
    fcout << "Constructed collar in  " << swCollar << std::endl;
    if(A_cubSetCR().embDim()<=3){
      Stopwatch swShaving;
      A_cubSetCR().shaveBI();
      fcout << "Shaving reduced the set to " << A_cubSetCR().cardinality() << " elementary cubes in " << swShaving << std::endl;
    }
    Stopwatch swConversion;
    CRef<P_CubCelSet> repSetCR( new P_CubCelSet(A_cubSetCR()) );
    fcout << "Changed cubSet to repSet in  " << swConversion << std::endl;
    return repSetCR;
  }

  static CubCelSet_CubSet_FunctorType CubCelSet_From_CubSet;

  // -------------------------------------------------------------------------------------- //

  static CRef<P_CubCelSet> CubCelSetReduce(CRef<P_CubCelSet> A_cubCelSetCR){

/*
    // With this one can remove boundary checks in isFreeFace, but the gain is smaller than the cost
    Stopwatch swCollar;
    A_cubCelSetCR().addEmptyCollar();
    fcout << "Collar added in " << swCollar <<  " \n";
*/

    Stopwatch swReduct;
int ncells=A_cubCelSetCR().cardinality();
fcout << "Reduction starting with " << ncells << " cells"  << std::endl;    // -- MM


/*  Commented out. For some reason does not help
fcout << "Starting reduce." << std::endl;
int loopsCnt=A_cubCelSetCR().reduce(1);
fcout << "  reduce() performed " << loopsCnt << " loops and reduced the set to " << A_cubCelSetCR().cardinality() << " cells.\n";
*/

    fcout << "Starting shaving via free face collapses." << std::endl;
    A_cubCelSetCR().shave();
    fcout << "Reduced in " << swReduct << " to " << A_cubCelSetCR().cardinality() << " cells.\n";

    Stopwatch swCoReduct;

    fcout << "Starting free coface collapses." << std::endl;
    A_cubCelSetCR().coReduceCompactSet();

    int nfcells=A_cubCelSetCR().cardinality();
    fcout << "  coReduceCompactSet reduced in " << swCoReduct << " to " << nfcells << " cells.\n";
    fcout << "  * * * Reduction factor is " << int(1000000*double(ncells-nfcells)/ncells+0.5)/10000.0 << "% * * * \n";

// It seems that nothing is left to coShave after coReduceCompactSet().

/*  ***
fcout << "Starting coShave." << std::endl;
while(int noPairsReduced=A_cubCelSetCR().coShave()){
  fcout << "  CoShave reduced " << noPairsReduced << " pairs" << std::endl;
}
*/


// !!!! Temporary code for peeking the outcome of reduction - should be commented out after every use !!!!
/*
P_CubCelSet cubCelSetCopy(A_cubCelSetCR()); // copy needed, because for some reason writing destroys the set
unsigned int repsetType='R'*256+'B'; // for representable sets
cubCelSetCopy.writeBmp("reduced.bmd",repsetType);
*/
// End of temporary code
// -- MM std::cout << "Reduction finished with \n" << A_cubCelSetCR() << std::endl;

    return A_cubCelSetCR;

  }

  static CubCelSet_CubCelSet_FunctorType CubCelSet_CR_CubCelSet;

  // -------------------------------------------------------------------------------------- //

  static CRef<ZGenRFCComplex> ZRFCComplexFromCubSet(CRef<P_CubSet> A_cubSetCR){

    Stopwatch sw;
    typename P_CubSet::PointCoordIterator it(A_cubSetCR());
    typename P_CubSet::PointCoordIterator itEnd=A_cubSetCR().end();
    std::vector<ElementaryCube> eCubes;
    int dim=A_cubSetCR().embDim();
    for(it=A_cubSetCR().begin();it<itEnd;++it){
      eCubes.push_back(ElementaryCube(it.coords(),dim));
    };
    Stopwatch sw1;
    fcout << "A vector of " << eCubes.size() << " elementary cubes constructed in " << sw  << std::endl;
    CRef<ZGenRFCComplex> rfccCR( new ZGenRFCComplex(eCubes));
    fcout << "Chain complex construction of CubSet completed in " << sw1  << std::endl;
    return rfccCR;

  }

  static RFCComplexOverZ_CubSet_FunctorType RFCComplexOverZ_From_CubSet;

  // -------------------------------------------------------------------------------------- //

  static CRef<ReducibleFreeChainComplexType> ReducibleFreeChainComplexFromCubCelSet(CRef<P_CubCelSet> A_cubCelSetCR){

    Stopwatch sw;
    CRef<ReducibleFreeChainComplexType> rfccCR( new ReducibleFreeChainComplexType(A_cubCelSetCR()));
    fcout << "Reducible free chain complex construction of CubCelSet completed in " << sw  << std::endl;
    return rfccCR;

  }

  static RFCComplex_CubCelSet_FunctorType RFCComplex_From_CubCelSet;

  // -------------------------------------------------------------------------------------- //

  static CRef<ReducibleFreeChainComplexType> ReducibleFreeChainComplexOverFieldFromCubCelSet(CRef<P_CubCelSet> A_cubCelSetCR){

    Stopwatch sw;

    CRef<ReducibleFreeChainComplexType> rfccCR( new ReducibleFreeChainComplexType( A_cubCelSetCR() ));
    A_cubCelSetCR =CRef<P_CubCelSet>(new P_CubCelSet); // to free memory
    // -- MMstd::cout << rfccCR()  << std::endl;
    fcout << "Reducible chain complex  construction of CubCelSet completed in " << sw  << std::endl;
    return rfccCR;

  }

  // -------------------------------------------------------------------------------------- //

  static CRef<ZGenRFCComplex> ReducibleFreeChainComplexOverZFromCubCelSet(CRef<P_CubCelSet> A_cubCelSetCR){

    // -- MMstd::cout << " Insertion starting "  << std::endl;
    Stopwatch sw;
    typename P_CubCelSet::PointCoordIterator it(A_cubCelSetCR());
    typename P_CubCelSet::PointCoordIterator itEnd=A_cubCelSetCR().end();
    std::set<GeneratorType> cells;
    int dim=A_cubCelSetCR().embDim();
    for(it=A_cubCelSetCR().begin();it<itEnd;++it){
    // -- MM std::cout << " Inserting "  << it << " in dim=" << dim << std::endl;
      cells.insert(GeneratorType(it.coords(),dim));
    };
    A_cubCelSetCR =CRef<P_CubCelSet>(new P_CubCelSet); // to free memory
    // -- MM std::cout << " rfccCR construction from " << cells.size() <<  " cells starting "  << std::endl;      // -- MM
    CRef<ZGenRFCComplex> rfccCR( new ZGenRFCComplex(cells));
    // -- MMstd::cout << rfccCR()  << std::endl;
    fcout << "Reducible chain complex (over Z) construction of CubCelSet completed in " << sw  << std::endl;
    return rfccCR;

  }

  static RFCComplexOverZ_CubCelSet_FunctorType RFCComplexOverZ_From_CubCelSet;

  // -------------------------------------------------------------------------------------- //


  static CRef<FreeChainComplexType> FreeChainComplexFromCubCelSet(CRef<P_CubCelSet> A_cubCelSetCR){

    Stopwatch sw;
    typename P_CubCelSet::PointCoordIterator it(A_cubCelSetCR());
    typename P_CubCelSet::PointCoordIterator itEnd=A_cubCelSetCR().end();
    std::set<GeneratorType> cells;
    int dim=A_cubCelSetCR().embDim();
    for(it=A_cubCelSetCR().begin();it<itEnd;++it){
      cells.insert(GeneratorType(it.coords(),dim));
    };
    CRef<FreeChainComplexType> fccCR( new FreeChainComplexType(cells));
    fcout << "Chain complex construction of CubCelSet completed in " << sw  << std::endl;
    return fccCR;

  }

  static FreeChainComplex_CubCelSet_FunctorType FreeChainComplex_From_CubCelSet;

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAlgebraicReductionsRandom(CRef<P_CubSet> A_setCR){
    return (
      HomAlgFunctors<ZGenFreeModule>::homSign_ArRandom_RFCComplex *
//      homSign_ArRandom_ZRFCComplex *
      RFCComplexOverZ_From_CubSet
    )(A_setCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAlgebraicReductionsSorted(CRef<P_CubSet> A_setCR){
    return (
      HomAlgFunctors<ZGenFreeModule>::homSign_ArSorted_RFCComplex *
//      homSign_ArSorted_ZRFCComplex *
      RFCComplexOverZ_From_CubSet
    )(A_setCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAlgebraicReductionsLocallySorted(CRef<P_CubSet> A_setCR){
    return (
      HomAlgFunctors<ZGenFreeModule>::homSign_ArLocallySorted_RFCComplex *
//      homSign_ArLocallySorted_ZRFCComplex *
      RFCComplexOverZ_From_CubSet
    )(A_setCR);
  }

  // -------------------------------------------------------------------------------------- //
  // For general use:
  static CRef<HomologySignatureType> HomologyViaAlgebraicReductions(CRef<P_CubSet> A_setCR){
    return (
      HomAlgFunctors<ZGenFreeModule>::homSign_ArRandom_RFCComplex *
//      homSign_ArRandom_ZRFCComplex *
      RFCComplexOverZ_From_CubSet
    )(A_setCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspace(CRef<P_CubSet> A_cubSetCR){

    Stopwatch swCollar;
    A_cubSetCR().addEmptyCollar();

    Stopwatch swShaving;
    if(shave){
      (A_cubSetCR().*shave)();
      fcout << "Shaving reduced the set to " << A_cubSetCR().cardinality() << " elementary cubes in " << swShaving << std::endl;
    }

    CRef<P_CubCelSet> cubCellSetCR;
    CRef<HomologySignatureType> homSignZeroCR(new HomologySignatureType());
    { // to save memory, we keep this local

      P_CubSet acyclicSubset(A_cubSetCR());
      Stopwatch swAcSubsp;
      // Now find the acyclic subset. Note: the acyclic subset is removed from the original set!
      int zeroBettiNumber=(A_cubSetCR().*acyclicSubspace)(acyclicSubset);
      lastAcyclicSubsetSize=acyclicSubset.cardinality();
      fcout << "Acyclic subsets of " << zeroBettiNumber << " components with " << lastAcyclicSubsetSize << " elementary cubes constructed in " << swAcSubsp << std::endl;

      // We got the zeroth betti numbers in zeroBettiNumber and now we store them in HomologySignatureType
      std::vector<int> t;
      homSignZeroCR().push_back(FGAGrpSignature<ScalarType> (zeroBettiNumber,t));

      Stopwatch swExcision;
      { // to save memory, keep this local
        // Construct the neighborhood of set-acyclicSubset
        P_CubSet wrapped(A_cubSetCR());
        wrapped.wrap();
        // Important are only these cubes in the acyclic subset, which intersect the difference
        acyclicSubset*=wrapped;
        // Now add back the trimmed acyclic subset to the set (it was removed when constructing the acyclic subset)
        A_cubSetCR()+=acyclicSubset;
      }
      fcout << "Excision completed in " << swExcision << std::endl;

      Stopwatch swConversion;
      cubCellSetCR=CRef<P_CubCelSet>(new P_CubCelSet(A_cubSetCR()));
      A_cubSetCR=CRef<P_CubSet>(new P_CubSet); // to free memory
      { // to save memory, we keep this local
        P_CubCelSet repAcyclicSubset(acyclicSubset);
        cubCellSetCR()-=repAcyclicSubset;
      }
      fcout << "Conversion to repset completed in " << swConversion << std::endl;
      // -- MM fcout << "Converted set has " << cubCellSetCR().cardinality() << " cells." << std::endl;
    }
    // Finally we call homSignViaAR and add the resulting hom signature to the zeroth betti numbers
    CRef<ZGenRFCComplex> zRFCComplexCR=ReducibleFreeChainComplexOverZFromCubCelSet(cubCellSetCR);
    CRef<HomologySignatureType> homSignCR=HomAlgFunctors<ZGenFreeModule>::homSignViaAR_Random(zRFCComplexCR);

    homSignCR()+=homSignZeroCR();

    return homSignCR;
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceOverField(CRef<P_CubSet> A_cubSetCR){

    Stopwatch swCollar;
    A_cubSetCR().addEmptyCollar();

    Stopwatch swShaving;
    if(shave){
      (A_cubSetCR().*shave)();
      fcout << "Shaving reduced the set to " << A_cubSetCR().cardinality() << " elementary cubes in " << swShaving << std::endl;
    }

    CRef<P_CubCelSet> cubCellSetCR;
    CRef<HomologySignatureType> homSignZeroCR(new HomologySignatureType());
    { // to save memory, we keep this local

      P_CubSet acyclicSubset(A_cubSetCR());
      Stopwatch swAcSubsp;
      // Now find the acyclic subset. Note: the acyclic subset is removed from the original set!
      int zeroBettiNumber=(A_cubSetCR().*acyclicSubspace)(acyclicSubset);
      lastAcyclicSubsetSize=acyclicSubset.cardinality();
      fcout << "Acyclic subsets of " << zeroBettiNumber << " components with " << lastAcyclicSubsetSize << " elementary cubes constructed in " << swAcSubsp << std::endl;

      // We got the zeroth betti numbers in zeroBettiNumber and now we store them in HomologySignatureType
      std::vector<int> t;
      homSignZeroCR().push_back(FGAGrpSignature<ScalarType> (zeroBettiNumber,t));

      Stopwatch swExcision;
      { // to save memory, keep this local
        // Construct the neighborhood of set-acyclicSubset
        P_CubSet wrapped(A_cubSetCR());
        wrapped.wrap();
        // Important are only these cubes in the acyclic subset, which intersect the difference
        acyclicSubset*=wrapped;
        // Now add back the trimmed acyclic subset to the set (it was removed when constructing the acyclic subset)
        A_cubSetCR()+=acyclicSubset;
      }
      fcout << "Excision completed in " << swExcision << std::endl;

      Stopwatch swConversion;
      cubCellSetCR=CRef<P_CubCelSet>(new P_CubCelSet(A_cubSetCR()));
      A_cubSetCR=CRef<P_CubSet>(new P_CubSet); // to free memory
      { // to save memory, we keep this local
        P_CubCelSet repAcyclicSubset(acyclicSubset);
        cubCellSetCR()-=repAcyclicSubset;
      }
      fcout << "Conversion to repset completed in " << swConversion << std::endl;
      // -- MM fcout << "Converted set has " << cubCellSetCR().cardinality() << " cells." << std::endl;
    }
    // Finally we call homSignViaAR and add the resulting hom signature to the zeroth betti numbers
    CRef<ReducibleFreeChainComplexType> fRFCComplexCR=ReducibleFreeChainComplexOverFieldFromCubCelSet(cubCellSetCR);
    CRef<HomologySignatureType> homSignCR=HomAlgFunctors<FreeModuleType>::homSignViaAR_Random(fRFCComplexCR);
    homSignCR()+=homSignZeroCR();

    return homSignCR;
  }

   // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceHOM(CRef<P_CubSet> A_cubSetCR){
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicHOM;
    shave=0;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceHOMShaved(CRef<P_CubSet> A_cubSetCR){
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicHOM;
    shave=&P_CubSet::shaveBCI;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceSI(CRef<P_CubSet> A_cubSetCR){
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicSI;
    shave=0;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  // The older version, working for one component only, is for some reason much faster than the above version
  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceSI_1C(CRef<P_CubSet> A_cubSetCR){
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicSI;
    shave=0;
    acyclicSubspace=&P_CubSet::acyclicSubspaceOrg;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  // The OSSI version (oversimplified simple intersection) works best in high dimensions, although
  // this may be just because the time is not wasted for the construction of the acyclic subset
  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceOSSIShaved(CRef<P_CubSet> A_cubSetCR){
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicOSSI;
    shave=&P_CubSet::shaveBCI;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceSI(CRef<P_CubCelSet> A_cubCellSetCR){
    CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()));
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicSI;
    shave=0;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceSI_1C(CRef<P_CubCelSet> A_cubCellSetCR){
    CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()));
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicSI;
    shave=0;
    acyclicSubspace=&P_CubSet::acyclicSubspaceOrg;
    return HomologyViaAcyclicSubspace(cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceSIShaved(CRef<P_CubSet> A_cubSetCR){
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicSI;
    shave=&P_CubSet::shaveBCI;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceSIShaved(CRef<P_CubCelSet> A_cubCellSetCR){
    CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()));
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicSI;
    shave=&P_CubSet::shaveBCI;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceSIR(CRef<P_CubSet> A_cubSetCR){
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicSIR;
    shave=0;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceSIRShaved(CRef<P_CubSet> A_cubSetCR){
    P_CubSet::neighbAcyclicBCI=&P_CubSet::neighbAcyclicSIR;
    shave=&P_CubSet::shaveBCI;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBCI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceLTD3(CRef<P_CubSet> A_cubSetCR){
    if(embeddingDim > 3 || embeddingDim < 1) throw std::runtime_error("This executable has been incorrectly compiled for embeddingDim different from 1, 2 or 3!");
    P_CubSet::neighbAcyclicBI=&P_CubSet::neighbAcyclicLT;
    shave=0;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceLTD3(CRef<P_CubCelSet> A_cubCellSetCR){
    if(embeddingDim > 3 || embeddingDim < 1) throw std::runtime_error("This executable has been incorrectly compiled for embeddingDim different from 1, 2 or 3!");
    CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()));
    P_CubSet::neighbAcyclicBI=&P_CubSet::neighbAcyclicLT;
    shave=0;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBI;
    return HomologyViaAcyclicSubspace(cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceLTD3Shaved(CRef<P_CubSet> A_cubSetCR){
    if(embeddingDim > 3 || embeddingDim < 1) throw std::runtime_error("This executable has been incorrectly compiled for embeddingDim different from 1, 2 or 3!");
    P_CubSet::neighbAcyclicBI=&P_CubSet::neighbAcyclicLT;
    shave=&P_CubSet::shaveBI;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBI;
    return HomologyViaAcyclicSubspace(A_cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceLTD3ShavedOverField(CRef<P_CubSet> A_cubSetCR){
    if(embeddingDim > 3 || embeddingDim < 1) throw std::runtime_error("This executable has been incorrectly compiled for embeddingDim different from 1, 2 or 3!");
    P_CubSet::neighbAcyclicBI=&P_CubSet::neighbAcyclicLT;
    shave=&P_CubSet::shaveBI;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBI;
    return HomologyViaAcyclicSubspaceOverField(A_cubSetCR);
  }


  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomologyViaAcyclicSubspaceLTD3Shaved(CRef<P_CubCelSet> A_cubCellSetCR){
    if(embeddingDim > 3 || embeddingDim < 1) throw std::runtime_error("This executable has been incorrectly compiled for embeddingDim different from 1, 2 or 3!");
    CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()));
    P_CubSet::neighbAcyclicBI=&P_CubSet::neighbAcyclicLT;
    shave=&P_CubSet::shaveBI;
    acyclicSubspace=&P_CubSet::acyclicSubspaceBI;
    return HomologyViaAcyclicSubspace(cubSetCR);
  }

  // -------------------------------------------------------------------------------------- //
  // Uses consecutive integers as generators codes
  static CRef<HomologySignatureType> HomSignViaRepSetReductions(CRef<P_CubSet> A_setCR){
    return (
      HomAlgFunctors<ZGenFreeModule>::homSign_ArRandom_RFCComplex *
      RFCComplexOverZ_From_CubCelSet *
      CubCelSet_CR_CubCelSet *
      CubCelSet_From_CubSet
    )(A_setCR);
  }

  // -------------------------------------------------------------------------------------- //
  // Uses generators directly as generator codes (but generators use internally only one integer)
  static CRef<HomologySignatureType> HomSignViaRepSetReductionsNew(CRef<P_CubSet> A_setCR){
    return (
      HomAlgFunctors<FreeModuleType>::homSign_ArRandom_RFCComplex *
      RFCComplex_From_CubCelSet *
      CubCelSet_CR_CubCelSet *
      CubCelSet_From_CubSet
    )(A_setCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomSignViaRepSetReductions(CRef<P_CubCelSet> A_setCR){
    CRef<P_CubCelSet>  A_setReducedCR=CubCelSetReduce(A_setCR);
    CRef<ZGenRFCComplex> zRFCComplexCR=ReducibleFreeChainComplexOverZFromCubCelSet(A_setReducedCR);
    return HomAlgFunctors<ZGenFreeModule>::homSignViaAR_Random(zRFCComplexCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomSignViaRepSetReductionsOverField(CRef<P_CubCelSet> A_setCR){
    CRef<P_CubCelSet>  A_setReducedCR=CubCelSetReduce(A_setCR);
    CRef<ReducibleFreeChainComplexType> fRFCComplexCR=ReducibleFreeChainComplexOverFieldFromCubCelSet(A_setReducedCR);
    return HomAlgFunctors<FreeModuleType>::homSignViaAR_Random(fRFCComplexCR);
  }

  // -------------------------------------------------------------------------------------- //

  static CRef<HomologySignatureType> HomSignViaRepSetReductionsFull(CRef<P_CubCelSet> A_cubCellSetCR){
    CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()));
    A_cubCellSetCR().~P_CubCelSet();
    cubSetCR().addEmptyCollar();
    return (
      HomAlgFunctors<ZGenFreeModule>::homSign_ArRandom_RFCComplex *
      RFCComplexOverZ_From_CubCelSet *
      CubCelSet_CR_CubCelSet *
      CubCelSet_From_CubSet
    )(cubSetCR);
  }
  // -------------------------------------------------------------------------------------- //

  static CRef<QuotientGradedModule<FreeModuleType> > HomologyViaRepSetReductions(CRef<P_CubCelSet> A_setCR){
    A_setCR().addEmptyCollar();
    return (
      HomAlgFunctors<FreeModuleType>::homology_Smith_FCComplex *
      FreeChainComplex_From_CubCelSet *
      CubCelSet_CR_CubCelSet
    )(A_setCR);
  }

};// class CubSetFunctors;

// Definition templates of static objects of CubSetFunctors class template

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
int CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::lastAcyclicSubsetSize=0;



template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
typename CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::CubCelSet_CubSet_FunctorType
  CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::CubCelSet_From_CubSet(
    &CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::BCubCelSetFromBCubSet
  );

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
typename CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::CubCelSet_CubCelSet_FunctorType
  CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::CubCelSet_CR_CubCelSet(
    &CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::CubCelSetReduce
  );

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
typename CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::RFCComplexOverZ_CubSet_FunctorType
  CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::RFCComplexOverZ_From_CubSet(
    &CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::ZRFCComplexFromCubSet
  );

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
typename CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::RFCComplex_CubCelSet_FunctorType
  CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::RFCComplex_From_CubCelSet(
    &CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::ReducibleFreeChainComplexFromCubCelSet
  );

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
typename CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::RFCComplexOverZ_CubCelSet_FunctorType
  CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::RFCComplexOverZ_From_CubCelSet(
    &CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::ReducibleFreeChainComplexOverZFromCubCelSet
  );

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
typename CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::FreeChainComplex_CubCelSet_FunctorType
  CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::FreeChainComplex_From_CubCelSet(
    &CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::FreeChainComplexFromCubCelSet
  );

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
typename CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::CubSetT_void_Ptr
  CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::shave(
    &P_CubSet::shaveBCI
  );

template<typename P_CubSet, typename P_CubCelSet, typename P_FreeChainComplex>
typename CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::CubSetT_CubSetT_Ptr
  CubSetFunctors<P_CubSet,P_CubCelSet,P_FreeChainComplex>::acyclicSubspace(
    &P_CubSet::acyclicSubspaceBCI
  );

// -------------------------------------------------------------------------------------- //
#endif //_CUBFUNCT_H_

/// @}

