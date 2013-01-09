/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ReducibleFreeChainComplex.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_REDUCIBLEFREECHAINCOMPLEX_H_)
#define _REDUCIBLEFREECHAINCOMPLEX_H_

// ********** class ReducibleFreeChainComplex ********** //

/*
 The class ReducibleFreeChainComplex in constrast to FreeChainComplex
 is designed for homology computations via reductions described in
    T. Kaczynski, M. Mrozek and M. \'Slusarek,
    Homology Computation by Reduction of Chain Complexes,
    Computers & Mathematics , 35(1998), no. 4, 59--70
  and
    M. Mrozek, K. Mischaikow and T. Kaczynski,
    Computational Homology,
    Applied Mathematical Sciences 157, Springer-Verlag, New York, 2004
  Therefore, unlike the objects of FreeChainComplex, the objects of
  ReducibleFreeChainComplex may change during computations.

   The chain complex is stored in the data structure

     std::vector<std::map<GeneratorCode,std::map<GeneratorCode,ScalarType> > >

   where GeneratorCode is either provided as the second template parameter or by default is taken to be
   egual to the generator type of the freeModuleType provided by the first template parameter;
   vector goes through all grades of the chain complex;
   the external map goes through all generators for a given grade
   and the internal map stores the boundary of this generator as pairs (generator,coefficient)
   for non-zero coefficients

   IMPORTANT: Out of the three constructor, the third one is designed to work with
   compact generators like ECellMDCode, designed when writing the code
   for filtrs and used in redhom. The old two constructors used in CrHom and AsHom
   require providing P_GeneratorCode (practically int) and cause the need
   for special ZGen* types in cubSetFunctors

*/

#include <list>
#include <queue>
#include "capd/homologicalAlgebra/ChainT.h"

template<typename freeModuleType, typename P_GeneratorCode>
class ReducibleFreeChainComplex;

template<typename freeModuleType, typename P_GeneratorCode>
void swap(ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>& A_rfcc1,ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>& A_rfcc2);

template<typename freeModuleType, typename P_GeneratorCode>
std::ostream& operator<<(std::ostream& out,const ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>& A_rfc);


template<typename freeModuleType, typename P_GeneratorCode=typename freeModuleType::GeneratorType>
class ReducibleFreeChainComplex{
  public:
    typedef P_GeneratorCode GeneratorCode;
    typedef freeModuleType FreeModuleType;
    typedef typename freeModuleType::GeneratorType GeneratorType;
    typedef typename freeModuleType::MatrixType MatrixType;
    typedef typename freeModuleType::MatrixType::ScalarType ScalarType;
    typedef ChainT<std::map<GeneratorCode,ScalarType> > Chain;
    typedef Chain CoChain;
    typedef typename std::map<GeneratorCode,Chain> GeneratorBoundaries;
    typedef typename std::map<GeneratorCode,CoChain> GeneratorCoBoundaries;
    typedef typename std::vector<GeneratorBoundaries> GradedGeneratorBoundaries;
    typedef typename std::vector<GeneratorCoBoundaries> GradedGeneratorCoBoundaries;
    typedef int (ReducibleFreeChainComplex::*ReducibleFreeChainComplex_void_Ptr)();

    // -------------------------------------------------------------------------------------- //

    ReducibleFreeChainComplex():m_storeReducedPairs(false){}

    /*
        This constructor constructs a reducible free chain complex from a chain complex
    */
    template<typename freeModuleType2>
    ReducibleFreeChainComplex(const FreeChainComplex<freeModuleType2>& fcc);

    /*  -------------------------------------------------------------------------------------- //
        This constructor takes a vector of generators as the argument.
        The generators are assumed to provide the method boundary(),
        returning the map mapping primary faces to their coefficients
        in the boundary
        Faces of all generators are assumed to be generators too.
        They are added to the list of generators automatically, so there is no need to add them
        to the input vector.
        Here it is assumed that generators themselves may be memory inefficient,
        so the generators are numbered by consecutive numbers and their numbers are
        used to build chains needed in the computations
        The correspondence between generators and their numbers (generator codes)
        are stored in a map
    */

    template<typename GeneratorType2>
    ReducibleFreeChainComplex(
      const std::vector<GeneratorType2>& A_gens // vector of generators
    );

    /* -------------------------------------------------------------------------------------- //
      This constructor takes a set of generators as the argument.
      The generators are assumed to know all their faces by providing the method primaryFaces()
      returning the vector of primary faces
      as well as the method boundary() returning the map mapping primary faces to their coefficients
      in the boundary
      Faces of generators are not automatically assumed to be generators in the chain complex, so
      all generators must be listed.
      The algebraic boundary in the chain module is taken to consists only of the faces present
      in the provided set. For this reason (search), set is taken here as the proper data structure
      on input
      No check is made if the provided set of generators leads to a correct chain complex!!! - should be changed!!!
    */

    template<typename GeneratorType2>
    ReducibleFreeChainComplex(
      const std::set<GeneratorType2>& A_gensSet // set of generators
    );

    /* -------------------------------------------------------------------------------------- //
      This constructor added on 2006-09-14.
      All previous constructors assume the GeneratorCode to be of integer type and
      the coding is performed by the constructors.
      In this constructor it is assumed that the GeneratorCode provided may be constructed
      from the GeneratorType provided inside the first template parameter.
      Actually, the simplest usage is to assume that the GeneratorCode coincides with the GeneratorType
      inside the first template parameter. This is efficient if the generatorType is efficient,
      like ECellMDCode which takes only one word.

      This constructor is designed to work with CubCellSetT class template provided by P_Set template
      argment but in the future may work with some other sets too.
      It takes as the argument the set of generators accessible via an iterator
      The generators must be convertible to the GeneratorCode obtained from the freeChainComplexType.

      The class GeneratorCode is assumed to provide the method boundary()
      returning the map mapping primary faces to their coefficients.
      Faces of generators are not automatically assumed to be generators in the chain complex, so
      all generators must be present in the provided set.
      The algebraic boundary in the chain module is taken to consists only of the faces present
      in the provided set.

      No check is made if the provided set of generators leads to a correct chain complex!!! - should be changed!!!
    */

    template<typename P_Set>
    ReducibleFreeChainComplex(
      const P_Set& A_set, // a set accessible via iterators
      int A_storeReducedPairs=false
    );

    /* -------------------------------------------------------------------------------------- //
       This operator converts the chain complex from the reducible chain complex representation
       to the free chain complex representation
    */

//    operator FreeChainComplex<FreeModule<GeneratorCode,Matrix<int,0,0> > >();
    operator FreeChainComplex<freeModuleType>();

    // ------------------------------------------------------------ //
    int topDim();


    // ------------------------------------------------------------ //
    void reducePair(
      int q, // grade in which the reduction is performed
      // iterator pointing to the first element of the reduction pair (b,a) or (coFace,face)
      // pointing to the external map
      typename GeneratorBoundaries::iterator coFacePos,
      // iterator pointing to the second element of the reduction pair (b,a) or (coFace,face)
      // pointing to the map storing the boundary of generator b
      typename Chain::iterator facePos
    );

    // ------------------------------------------------------------ //
    // This is a direct implementation of the KMS algorithm
    int reduce();

    // ------------------------------------------------------------ //
    // This measures the amount of work needed to make the change of the boundary operator when reducing
    int findMeasure(const int& coFaceDim,const GeneratorCode& coFace, const GeneratorCode& face);

    // ------------------------------------------------------------ //
    // An auxiliary class for storing reduced pairs, needed in filtration
    friend class ReducedPair;
    class ReducedPair;

    // ------------------------------------------------------------ //
    // An auxiliary class for selecting pairs to reduce (see the code of reduceViaSort)
    friend class ReduciblePair;
    class ReduciblePair;

    void extractReduciblePairsInVicinityOf(
      int dim,
      GeneratorCode g,
      std::set<ReduciblePair>& source,
      std::list<ReduciblePair>& destination
    );

    // ------------------------------------------------------------ //
    // Here we first search for all the reducible pairs and sort them
    // according to the measure defined above. Then we reduce the reducible
    // pairs starting from the pair with the lowest measure
    // We keep updating the measure and position in the priority queue
    // after every reduction
    int reduceViaSort();

    // ------------------------------------------------------------ //
    // Find the first reducible pair, reduce it, search for new reducible
    // pairs in the vicinity of the reduced coFace, choose the one with smallest
    // measure and proceed this way until no reducible pairs are found
    int reduceViaLocalSort();

    // ------------------------------------------------------------ //
    // Search if a reducible pair of any type exists, if so return true
    // reduce all reducible pairs of the prescribed coboundary size
    // It may happen that no pairs are reduced, but some reducible pairs exist
    bool reduceViaStack(unsigned int searchedCoboundrySize, int& pairsReduced);

    // ------------------------------------------------------------ //
    void reduceFromBottom();

    // ------------------------------------------------------------ //
    // Generators, which have zero boundary and coboundary are simple homology generators
    // All these generators can be removed from the complex
    // What remains is still a complex
    // The total homology is the homology given by the simple homology generators plus the homology of
    // what is left.
    // Return true if all generators were removed
    bool removeSimpleHomologyGenerators(std::vector<std::vector<GeneratorCode> >& simpleHomologyGenerators);

    // ------------------------------------------------------------ //
    friend void swap<freeModuleType,P_GeneratorCode>(
      ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>& A_rfcc1,
      ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>& A_rfcc2
    );
    friend std::ostream& operator<< <freeModuleType,P_GeneratorCode>(
      std::ostream& out,
      const ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>& A_rfc
    );

    void storeReducedPair(
      int A_coFaceDim,
      GeneratorCode A_coFace,
      GeneratorCode A_face,
      const Chain& A_bdy,
      const CoChain& A_cbdy,
      ScalarType A_lambda
    );
    void reduce(Chain& A_chain);
    void restore(Chain& A_chain);
  // ------------------------------------------------------------ //
//  private:
    GradedGeneratorBoundaries m_ggb;
    GradedGeneratorCoBoundaries m_ggCb;
    bool m_storeReducedPairs;
    std::vector<ReducedPair> m_reducedPairs;
};//ReducibleFreeChainComplex

// ++++++++++++++++++++++++++++ Internal class ReducedPair +++++++++++++++++++++++++++++++++++++ //

// Note: this code is more general than the code in the class template ReductionPairT,
// but is slower. Both, ReductionPairT and ReducedPair are needed

template<typename freeModuleType, typename P_GeneratorCode>
class ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::ReducedPair{
  int coFaceDim;
  GeneratorCode coFace,face;
  Chain coFaceBoundary;      // coface boundary is stored multiplied by the reduction coefficient lambda
  CoChain faceCoBoundary;    // face coboundary is stored multiplied by the reduction coefficient lambda

  public:
  ReducedPair(
    int A_coFaceDim,
    GeneratorCode A_coFace,
    GeneratorCode A_face,
    const Chain& A_bdy,
    const CoChain& A_cbdy,
    ScalarType A_lambda
  ):coFaceDim(A_coFaceDim),coFace(A_coFace),face(A_face),coFaceBoundary(A_bdy),faceCoBoundary(A_cbdy){
     coFaceBoundary*=A_lambda; // multiply here by lambda for efficiency reasons
     faceCoBoundary*=A_lambda; // multiply here by lambda for efficiency reasons
  }

  void reduce(Chain& A_chain){
    // -- fcout << " RFCC Reducing through pair (" << face << "," << coFace << ")\n"; //--
    int chainOwnDim=A_chain.ownDim();
    if(chainOwnDim==coFaceDim-1){
      // -- fcout << " RFCC Reduced by (" << A_chain.at(face)*coFaceBoundary << "\n"; //--
      A_chain-=A_chain.at(face)*coFaceBoundary; //  lambda already stored in boundary
      // A_chain.erase(face); // not needed, guaranteed by the above instruction
    }else if(chainOwnDim==coFaceDim){
      // -- fcout << " RFCC Reduced by (" << coFace << "\n"; //--
      A_chain.erase(coFace);
    }

  }

  void restore(Chain& A_chain){
    int chainOwnDim=A_chain.ownDim();
    if(chainOwnDim==coFaceDim){
      ScalarType s=A_chain*faceCoBoundary;
      A_chain[coFace]-=s; //  lambda already stored in coboundary
    }
  }
/*
  const GeneratorCode& CoFace(){
    return coFace;
  }
  const GeneratorCode& Face(){
    return face;
  }
  const int& CoFaceDim(){
    return coFaceDim;
  }
*/
};

// ++++++++++++++++++++++++++++ Internal class ReduciblePair +++++++++++++++++++++++++++++++++++++ //

template<typename freeModuleType, typename P_GeneratorCode>
class ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::ReduciblePair{
  int coFaceDim;
  GeneratorCode coFace,face;
  int measure;

  public:
  ReduciblePair(
    int A_coFaceDim,GeneratorCode A_coFace,GeneratorCode A_face,int A_measure):
    coFaceDim(A_coFaceDim),coFace(A_coFace),face(A_face),measure(A_measure){}

  friend bool operator<(const ReduciblePair& p1,const ReduciblePair& p2){
    if(p1.measure !=  p2.measure) return p1.measure < p2.measure;
    if(p1.coFace  !=  p2.coFace) return p1.coFace  <  p2.coFace;
    return p1.face  <  p2.face;
  }
  friend bool operator>(const ReduciblePair& p1,const ReduciblePair& p2){
    if(p1.measure !=  p2.measure) return p1.measure > p2.measure;
    if(p1.coFace  !=  p2.coFace) return p1.coFace  >  p2.coFace;
    return p1.face  >  p2.face;
  }
  const GeneratorCode& CoFace(){
    return coFace;
  }
  const GeneratorCode& Face(){
    return face;
  }
  const int& CoFaceDim(){
    return coFaceDim;
  }
  void setMeasure(int m){
    measure=m;
  }
};

// ++++++++++++++++++++++++++++ inline functions definitions +++++++++++++++++++++++++++++++++++ //

template<typename freeModuleType, typename P_GeneratorCode>
int ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::topDim(){
  return m_ggb.size()-1;
}

// ------------------------------------------------------------ //

template<typename freeModuleType2, typename GeneratorCode2>
inline void swap(ReducibleFreeChainComplex<freeModuleType2,GeneratorCode2>& A_rfcc1,ReducibleFreeChainComplex<freeModuleType2,GeneratorCode2>& A_rfcc2){
  std::swap(A_rfcc1.m_ggb,A_rfcc2.m_ggb);
  std::swap(A_rfcc1.m_ggCb,A_rfcc2.m_ggCb);
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
inline void ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::storeReducedPair(
  int A_coFaceDim,
  GeneratorCode A_coFace,
  GeneratorCode A_face,
  const Chain& A_bdy,
  const CoChain& A_cbdy,
  ScalarType A_lambda
){
  m_reducedPairs.push_back(ReducedPair(A_coFaceDim,A_coFace,A_face,A_bdy,A_cbdy,A_lambda));
}

// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
inline void ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::reduce(Chain& A_chain){
  for(unsigned int i=0;i<m_reducedPairs.size();++i){
    m_reducedPairs[i].reduce(A_chain);
  }
}
// ------------------------------------------------------------ //

template<typename freeModuleType, typename P_GeneratorCode>
inline void ReducibleFreeChainComplex<freeModuleType,P_GeneratorCode>::restore(Chain& A_chain){
  for(int i=m_reducedPairs.size()-1;i>=0;--i){
    m_reducedPairs[i].restore(A_chain);
  }
}

// ------------------------------------------------------------ //

#endif //_REDUCIBLEFREECHAINCOMPLEX_H_
/// @}

