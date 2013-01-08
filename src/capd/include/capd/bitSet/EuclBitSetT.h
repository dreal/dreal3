/// @addtogroup matrixAlgorithms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSetT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_BITSET_EUCLBITSETT_H_
#define _CAPD_BITSET_EUCLBITSETT_H_

#include <vector>
#include <fstream>
#include <stack>
#include <list>

#include "capd/auxil/ofstreamcout.h"

#include "capd/repSet/RepSet.h"
#include "capd/repSet/ElementaryCube.h"
#include "capd/bitSet/BitSetT.h"
#include "capd/bitSet/BitmapT.h"

#undef begin
#undef end

using std::vector;
extern ofstreamcout fcout;

template <typename P_BitSet,int dim>
class EuclBitSetT;

template <typename P_BitSet,int dim>
void showBmpCubSet(const EuclBitSetT<P_BitSet,dim>& set,int color,bool clear=true);

template <typename P_BitSet,int dim>
void showBmpCubSet(const EuclBitSetT<P_BitSet,dim>& set,int color,bool clear,bool rescale=true);

template <typename P_BitSet,int dim>
std::istream& operator>>(std::istream& in,EuclBitSetT<P_BitSet,dim>& A_BmpCubSet);


template <typename P_BitSet,int dim>
class EuclBitSetT : public P_BitSet{
public:
  typedef typename P_BitSet::Word Word;
  typedef typename P_BitSet::WordIterator WordIterator;
  typedef bool (*selectorType)(const int*);
  typedef P_BitSet BaseClass;
  typedef P_BitSet BitmapType;
  typedef const int* Point;

  struct Pixel;
  class interval;
  class BitIterator;
  class PointIterator;
  class NeighbIterator;
//  class BdNeighbIterator;   // BdNeighbIterator does not work correctly yet
  class PointCoordIterator;
  class BitCoordIterator;
  class BitParIterator;
  class PointParIterator;
  class HypPlBitIterator;  // for iterating over hyperplanes

  friend class BitIterator;
  friend class NeighbIterator;
  friend class PointCoordIterator;

protected:
  static const int bitsPerWord=sizeof(Word)*8;
  static const int neighbCubeInitPosition=(dim>=3 ? 0 : 9+3*(dim==1)); // should be respectively 0,9,12 for dimensions 3,2,1
                                                                       // used only for these dimensions in CubSetT<P_EuclSet>::neighbAcyclicLT method
  int paddedBitWidth[dim];    // width in pixels in every dimension
  int wordWidth[dim];         // width in words in every dimension
                              // Note: wordWidth[i]==paddedBitWidth[i] for i!=0
  int wordStride[dim];        // the directional shifts for the bitCoordIterator;
  int sumBitStrides;          // sum of all bit strides for initialising nieghbBegin and neighbEnd iterators
  int neighbStride[dim];      // the directional shifts for the NeighbIterator;
  int actualDimZeroBitWidth;  // indicates the true width in dim zero
                              // Note: paddedBitWidth[0] is a multiplicity of bitsPerWord for the sake of efficiency

  struct PixelNeighborOffset;
  void setupWidths();
  void setupStrides();

public:
  using P_BitSet::Length;

  static const int theDim=dim;
  explicit EuclBitSetT(int size=0,bool clear=false);   // BitmapT with size pixels in each dimension
  explicit EuclBitSetT(const int* w,bool clear=false); // BitmapT with w[i] pixels in dimension i
  explicit EuclBitSetT(const int* w, const char* bytes); // BitmapT with w[i] pixels in dimension i, using a provided bitmap
  EuclBitSetT(const EuclBitSetT& org, bool clear=false);
  EuclBitSetT(const EuclBitSetT& org,const Pixel& lc,const Pixel& uc);
  EuclBitSetT(const EuclBitSetT& org,const std::vector<int>& lc,const std::vector<int>& uc);
  EuclBitSetT(const RepSet<ElementaryCube>& A_RepSetOfElementaryCube);

/*
  template <typename P_Chain>
  EuclBitSetT(const P_Chain& chain, const EuclBitSetT& space);
*/

  const BaseClass& getBaseObject() const{ return *static_cast<const BaseClass*>(this);}

  int embDim() const{ return dim;}
  const int* Dimensions(){ return paddedBitWidth; }
  const P_BitSet& getBitSet() const{ return *(P_BitSet*)(this);}
  unsigned long int getBmpSizeInBits(){ return this->length*bitsPerWord; }
  unsigned long int getBmpSizeInBytes(){ return this->length*sizeof(Word); }

  EuclBitSetT<P_BitSet,dim>& invert(bool trim=false){
    P_BitSet::invert();
    if(!trim) actualDimZeroBitWidth=paddedBitWidth[0];
    return *this;
  }

  BitIterator begin() const{
    return typename EuclBitSetT<P_BitSet,dim>::BitIterator(this->P_BitSet::begin());
  }

  BitIterator end() const{
    return typename EuclBitSetT<P_BitSet,dim>::BitIterator(this->P_BitSet::end());
  }

  NeighbIterator neighbBegin(const BitIterator& it) const{
    NeighbIterator nIt(*this,it);
    nIt+=-nIt.baseEuclBitSet()->sumBitStrides;
    return nIt;
  }

  NeighbIterator neighbEnd(const BitIterator& it) const{
    NeighbIterator nIt(*this,it);
    nIt+=nIt.baseEuclBitSet()->sumBitStrides;
    ++nIt;
    return nIt;
  }

  HypPlBitIterator hypPlBegin(int coords[]) const{
    HypPlBitIterator nIt(*this,coords);
    return nIt;
  }

/*
  HypPlBitIterator hypPlEnd() const{
    // The HypPlBitIterator is always set to end of bitmap when reaching the end of hyperplane
    // So we may safely return the end of bitmap
std::cout << "hypPlEnd" << std::endl;
    return this->end();
  }
*/

/*    // BdNeighbIterator does not work correctly yet
  BdNeighbIterator bdNeighbBegin(const BitCoordIterator& it) const{
    BdNeighbIterator nIt(*this,it,0);
    return nIt;
  }

  BdNeighbIterator bdNeighbEnd(const BitCoordIterator& it) const{
    BdNeighbIterator nIt(*this,it,2);
    ++nIt;
    return nIt;
  }
*/

  EuclBitSetT& wrap();
  EuclBitSetT& peel();

  int getPaddedWidth(int i) const;
  int getUnpaddedWidth(int i) const;

  EuclBitSetT& operator=(const EuclBitSetT& A_EuclBitSet2);

  void addPixel(const Pixel& p);
  void removePixel(const Pixel& p);
  bool containsPixel(const Pixel& p) const;

  void insert(const Point& p);
  void remove(const Point& p);
  bool contains(const Point& p) const;

  void addBox(const Pixel& lc,const Pixel& uc);
  void addBoxBoundary(const Pixel& lc,const Pixel& uc);

  template<typename Selector>
  EuclBitSetT& add(const Selector& s,bool clear=false);

  void readBmp(const char* fileName);
  void writeBmp(const char* fileName,unsigned int A_type);


  bool findSomePoint(Pixel& p) const;
  bool midPoint(Pixel& p) const;
  bool contains(const Pixel& p) const;


  template<typename word2, int dim2>
  friend void showBmpCubSet(const EuclBitSetT<word2,dim2>& set,int color,bool clear,bool rescale);

  template<typename word2, int dim2>
  friend void showBmpCubSet(const EuclBitSetT<word2,dim2>& set,int color,bool clear);

  friend std::istream& operator>> <P_BitSet>(std::istream& in,EuclBitSetT<P_BitSet,dim>& A_BmpCubSet);

  /* ------------------------  ------------------------ */
  friend std::ostream& operator<<(std::ostream& out,const EuclBitSetT& A_BmpCubSet){
//    typename EuclBitSetT<P_BitSet,dim>::PointCoordIterator it(A_BmpCubSet);
    PointCoordIterator it(A_BmpCubSet);
    for(it=A_BmpCubSet.begin();it<A_BmpCubSet.end();++it){
      out << "(" << it[0];
      for(int i=1;i<dim;++i){
        out << "," << it[i];
      }
      out << ")" << std::endl;
    };
    return out;
  }

  /* ------------------------  ------------------------ */
  friend void swap(EuclBitSetT& A_BmpCubSet1,EuclBitSetT& A_BmpCubSet2){
    swap(static_cast<P_BitSet&>(A_BmpCubSet1),static_cast<P_BitSet&>(A_BmpCubSet2));
    std::swap(A_BmpCubSet1.actualDimZeroBitWidth,A_BmpCubSet2.actualDimZeroBitWidth);
    std::swap(A_BmpCubSet1.sumBitStrides,A_BmpCubSet2.sumBitStrides);
    for(int i=0;i<dim;++i){
      std::swap(A_BmpCubSet1.paddedBitWidth[i],A_BmpCubSet2.paddedBitWidth[i]);
      std::swap(A_BmpCubSet1.wordWidth[i],A_BmpCubSet2.wordWidth[i]);
      std::swap(A_BmpCubSet1.wordStride[i],A_BmpCubSet2.wordStride[i]);
      std::swap(A_BmpCubSet1.neighbStride[i],A_BmpCubSet2.neighbStride[i]);
    }
  }

  /* ------------------------  ------------------------ */
  void clearHypPl(int coords[]){
    HypPlBitIterator it(*this,coords);
    if(coords[0]<0){ // We go through the whole 0 direction, so we can jump by words
      for(;it<end();it.nextWord()){
        *(Word*)(it)=0;
      }
    }else{
      for(;it<end();++it){
        it.setBit(0);
      }
    }
  }

  /* ------------------------  ------------------------ */
  template<int dimF>
  void clearFiber(const EuclBitSetT<P_BitSet,dimF>& A_fibSet){
      for(typename EuclBitSetT<P_BitSet,dimF>::PointCoordIterator it=A_fibSet.begin();it<A_fibSet.end();++it){
        int codim=dim-dimF;
        int hypPlane[dim];
        for(int i=0;i<dim;++i){
          //  hypPlane[i] = (i<domEmbDim ? it[i] : -1);              // For XY order in graph - keep it just in case  - needs changes in 2 other places
          hypPlane[i] = (i-codim>=0 ? it[i-codim] : -1);     // For YX order in graph - more efficient
        }
        clearHypPl(hypPlane);
      }
  }

  /* ------------------------  ------------------------ */
  bool isZeroHypPl(int coords[]){
    HypPlBitIterator it(*this,coords);
    if(coords[0]<0){ // We go through the whole 0 direction, so we can jump by words
      for(;it<end();it.nextWord()){
        if(*(Word*)(it)!=0) return false;
      }
    }else{
      for(;it<end();++it){
        if(it.getBit()!=0) return false;
      }
    }
    return true;
  }
};

/************************************************************************************/

template <typename P_BitSet,int dim>
inline void EuclBitSetT<P_BitSet,dim>::insert(const Point& p){
  BitCoordIterator it(*this,p);
  it.setBit();
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline void EuclBitSetT<P_BitSet,dim>::remove(const Point& p){
  BitCoordIterator it(*this,p);
  it.clearBit();
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline bool EuclBitSetT<P_BitSet,dim>::contains(const Point& p) const{
  BitCoordIterator it(*this,p);
  return it.getBit();
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline void EuclBitSetT<P_BitSet,dim>::addPixel(const Pixel& p){
  BitCoordIterator it(*this,p);
  it.setBit();
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline void EuclBitSetT<P_BitSet,dim>::removePixel(const Pixel& p){
  BitCoordIterator it(*this,p);
  it.clearBit();
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline bool EuclBitSetT<P_BitSet,dim>::containsPixel(const Pixel& p) const{
  BitCoordIterator it(*this,p);
  return it.getBit();
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline int EuclBitSetT<P_BitSet,dim>::getPaddedWidth(int i) const{
  return paddedBitWidth[i];
}

/************************************************************************************/

template <typename P_BitSet,int dim>
inline int EuclBitSetT<P_BitSet,dim>::getUnpaddedWidth(int i) const{
  return (i ? paddedBitWidth[i]:actualDimZeroBitWidth);
}

/************************************************************************************/

/*
template <typename P_BitSet,int dim>
inline typename EuclBitSetT<P_BitSet,dim>::BitIterator EuclBitSetT<P_BitSet,dim>::begin() const{
  return typename EuclBitSetT<P_BitSet,dim>::BitIterator(this->P_BitSet::begin());
}
*/

/************************************************************************************/

/*
template <typename P_BitSet,int dim>
inline typename EuclBitSetT<P_BitSet,dim>::BitIterator EuclBitSetT<P_BitSet,dim>::end() const{
  return typename EuclBitSetT<P_BitSet,dim>::BitIterator(this->P_BitSet::end());
}
*/


/************************************************************************************/

/*
template <typename P_BitSet,int dim>
inline typename EuclBitSetT<P_BitSet,dim>::NeighbIterator EuclBitSetT<P_BitSet,dim>::neighbBegin(const BitIterator& it) const{
  NeighbIterator nIt(*this,it);
  nIt+=-nIt.baseEuclBitSet()->sumBitStrides;
  return nIt;
}
*/

/************************************************************************************/

/*
template <typename P_BitSet,int dim>
inline typename EuclBitSetT<P_BitSet,dim>::NeighbIterator EuclBitSetT<P_BitSet,dim>::neighbEnd(const BitIterator& it) const{
  NeighbIterator nIt(*this,it);
  nIt+=nIt.baseEuclBitSet()->sumBitStrides;
  ++nIt;
  return nIt;
}
*/

/************************************************************************************/

#include "capd/bitSet/EuclBitSetPixelNeighborOffset.h"
#include "capd/bitSet/EuclBitSet_Pixel.h"
#include "capd/bitSet/EuclBitSet_BitIterator.h"
#include "capd/bitSet/EuclBitSet_PointIterator.h"
#include "capd/bitSet/EuclBitSet_BitCoordIterator.h"
#include "capd/bitSet/EuclBitSet_PointCoordIterator.h"
//#include "capd/bitSet/EuclBitSet_BitParIterator.h"
//#include "capd/bitSet/EuclBitSet_PointParIterator.h"
#include "capd/bitSet/EuclBitSet_NeighbIterator.h"
#include "capd/bitSet/EuclBitSet_HypPlBitIterator.h"
#include "capd/bitSet/BmpHeader.hpp"
#include "capd/bitSet/EuclBitSet_interval.h"
#include "capd/bitSet/EmbDimException.h"
#include "capd/multiEngHom/powerTwoCeiling.h"



#endif // _CAPD_BITSET_EUCLBITSETT_H_

/// @}

