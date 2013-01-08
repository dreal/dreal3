/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CubCellSetT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#if !defined(_CUB_CELL_SET_H_)
#define _CUB_CELL_SET_H_

#include "capd/bitSet/EuclBitSetT.h"
#include "capd/repSet/RepSet.h"
#include <stack>

#include "capd/bitSet/ReductionPairT.h"
#include "capd/bitSet/CubFaceIndex.h"
#include "capd/homologicalAlgebra/embeddingDim.h"
#include "capd/homologicalAlgebra/ChainT.h"


template <typename P_EuclSet>
class CubSetT;


template <typename P_EuclSet,typename P_Reductor=void*> // P_Reductor:
                                            //   void* - original version,
                                            //   ReductionPairT<CubeFaceIndex> - reduction pairs recording version
class CubCellSetT : public P_EuclSet{
public:
  std::vector<P_Reductor> reductors;
public:
  typedef typename P_EuclSet::Pixel Pixel;
  typedef typename P_EuclSet::BitCoordIterator BitCoordIterator;
  typedef typename P_EuclSet::BitParIterator BitParIterator;
  typedef typename P_EuclSet::BitIterator BitIterator;
  typedef typename P_EuclSet::PointIterator PointIterator;
  typedef typename P_EuclSet::PointCoordIterator PointCoordIterator;
  typedef typename P_EuclSet::PointParIterator PointParIterator;
  typedef typename P_EuclSet::NeighbIterator NeighbIterator;
  typedef typename P_EuclSet::Word Word;
  typedef P_Reductor ReductorType;
  typedef P_EuclSet BaseClass;
  typedef typename P_EuclSet::BaseClass::BaseClass BitmapType;

  static const int theDim=P_EuclSet::theDim;

//  CubCellSetT():P_EuclSet(){};
  CubCellSetT(const int* A_w, bool clear=false):P_EuclSet(A_w,clear){}  // BitmapT with w[i] pixels in dimension i
  CubCellSetT(const CubCellSetT& A_org, bool clear=false);
  CubCellSetT(int size=0, bool clear=false):P_EuclSet(size,clear){}      // BitmapT with size pixels in each dimension
  CubCellSetT(const P_EuclSet& A_EuclSet);
  CubCellSetT(const CubCellSetT& org, const std::vector<int>& lc, const std::vector<int>& uc):P_EuclSet(org,lc,uc){}
  CubCellSetT(const RepSet<ElementaryCube>& A_RepSetOfElementaryCube);
  CubCellSetT(const RepSet<ElementaryCell>& A_RepSetOfElementaryCell);

  template<class ChainContainer>
  void fillWith(const ChainT<ChainContainer>& chain);

  const std::vector<P_Reductor>& getReductors() const{ return reductors;}
  const BaseClass& getBaseObject() const{ return *static_cast<const BaseClass*>(this);}

  // Conversion to the full cubical set obtained
  // by treating each cell as a full cube  (very unsafe, should not be used together with CRef !!!)
/*
  operator P_EuclSet&(){
    return *reinterpret_cast<P_EuclSet* >(this);
  }
*/

  void addEmptyCollar();
  void rescale(int A_factor);
  void rescale(const int A_factor[]);

  // Verify if the given pixel represents a vertex in the
  // representalbe set, i.e. if it is degenerate in all dimensions

  // Iterator version
  bool isVertex(BitCoordIterator& A_it) const;

  // Verify if the given pixel represents a maximal cell in the
  // representalbe set, i.e. if it is not a face of a cell of dimesion one greater
  bool isMaximal(BitCoordIterator& A_it) const;

  // Verify if the given pixel represents a free cell in the representable set,
  // i.e. a cell which is a face of exaclty one cell of dimension one greater
  // (codimension one coface)
  // If true, return the codimension one coface
  bool isFreeFace(BitCoordIterator& A_faceIt, BitCoordIterator& A_coFaceIt) const;

  // Verify if the given pixel represents a cofree cell in the representable set,
  // i.e. a cell which has exaclty one face of dimension one lower in the representable set
  // (codimension one face)
  // If true, return the codimension one face

  bool findCoFreeFaceOrFreeVertex(const CubCellSetT& source,PointIterator& A_startIter,BitCoordIterator& A_it)const;

  // Iterator version
  bool isFreeCoFace(BitCoordIterator& A_it, BitCoordIterator& A_codimOneFaceIt) const;


  // Iterator version
  void getCoFaces(BitCoordIterator& A_it,std::vector<BitCoordIterator>& A_codimOneCofacesIterators) const;

  // Find all codim one faces of a given pixel
  void getFaces(BitCoordIterator& A_it,std::vector<BitCoordIterator>& A_facesIterators) const;

  // Add boundaries of every top dim cell to the set
  void fillWithSubEmbDimCells();
  // A specialized version of shave for representable sets
  void fillWithBoundaries();
  // A specialized version of shave for representable sets

  int shave();
  // A dual version of shave for representable sets
  int coShave();

  // remove reduction pairs via BFS
//  int reduce();

  // remove reduction pairs via BFS wit a limit of repetitions
  int reduce(int limit=0);
  // remove coreduction pairs via BFS
  int coReduce();       // iterator version

  // A speeded up version for compact sets
  bool findFreeCoFace(PointIterator& A_startIter,BitCoordIterator& A_it) const;
  bool findVertex(PointIterator& A_startIter,BitCoordIterator& A_it) const;
  int coReduceCompactSet();
  int coReduceCompactSetFast();

  // A method for storing reduction pairs
  void removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt);

  // Auxiliary, recursive method for cubicalClosureSkeleton
  bool belongsToCubicalClosure(BitCoordIterator& A_it);

  // Given a CubRepSet consisting of vertices only, compute
  // the A_skeletonDimension skeleton of the cubical closure
  // defined by the recursive formula that a cube belongs to the
  // closure if all it faces belong to the closure
  void cubicalClosureSkeleton(int A_skeletonDimension);

  template<typename P_Chain>
  void reduce(P_Chain& A_chain);

  template<typename P_Chain>
  void reduceInDimZero(P_Chain& A_chain);

  template<typename P_Chain>
  void restore(P_Chain& A_chain);


  friend std::ostream& operator<<(std::ostream& out,const CubCellSetT<P_EuclSet,P_Reductor>& A_BmpCubSet){
    typename CubCellSetT<P_EuclSet,P_Reductor>::PointCoordIterator it(A_BmpCubSet);
    int dim=A_BmpCubSet.embDim();
    for(it=A_BmpCubSet.begin();it<A_BmpCubSet.end();++it){
      for(int i=0;i<dim;++i){
        int k=it[i]/2;
        if(2*k==it[i]){
          out << "[" << k << "]";
        }else{
          out << "(" << k << "," << k+1 << ")";
        }
        if(i<dim-1)  out << "x";
      }
      out << std::endl;
    };
    return out;
  }

  friend void swap(CubCellSetT& A_set1,CubCellSetT& A_set2){
    swap(*static_cast<P_EuclSet*>(&A_set1),*static_cast<P_EuclSet*>(&A_set2));
  }
};

// -------------------------------------------------------------------------------------- //

// ********** Inline methods definitions ********** //

/************************************************************************************/
typedef unsigned long int cluster;
typedef BitSetT<BitmapT<cluster> > BitSet;
typedef EuclBitSetT<BitSet,embeddingDim> EuclBitSet;
typedef CubSetT<EuclBitSet> BCubSet;
typedef CubCellSetT<EuclBitSet> BCubCelSet;

/************************************************************************************/

// Unfortunately gcc (or the current C++ standard) does not allow for partial specialization
// of metods, so here is the specialization of removeReductionPair for dimensions 2 to 12
// If needed, more specializations have to be added here

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,2>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,3>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,4>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,5>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,6>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,7>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,8>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,9>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,10>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,11>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,12>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,13>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,14>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}

template<>
inline void CubCellSetT<EuclBitSetT<BitSet,15>,void*>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
}




/************************************************************************************/
// Warning: a specialization is needed for P_Reductor=void* !!!
// Such specializations for dimensions 2 to 15 are added above

template <typename P_EuclSet,typename P_Reductor>
inline void CubCellSetT<P_EuclSet,P_Reductor>::removeReductionPair(BitCoordIterator& A_freeFaceIt,BitCoordIterator& A_companionFaceIt){
  typedef typename P_Reductor::CubeFaceIndexType CubeFaceIndexType;
  A_freeFaceIt.clearBit();
  A_companionFaceIt.clearBit();
  // -- fcout << "Reducing through " << A_freeFaceIt << "," <<A_companionFaceIt << std::endl;  // -- MM
/*
CubeFaceIndexType freeFaceIndex(A_freeFaceIt);
CubeFaceIndexType companionFaceIndex(A_companionFaceIt);
fcout << "Reduced through indexes" << freeFaceIndex << "," << companionFaceIndex << std::endl;  // -- MM
*/
  reductors.push_back(P_Reductor(A_freeFaceIt,A_companionFaceIt));
  // --
}

/************************************************************************************/


#endif // _CUB_CELL_SET_H_
/// @}

