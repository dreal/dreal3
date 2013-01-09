/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_BitIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_EUCLBITSET_BITITERATOR_H_)
#define _EUCLBITSET_BITITERATOR_H_
#include "capd/bitSet/CubFaceIndex.h"

/*=======================================================================*/
// BitIterator is a BitmapT iterator
// intended for fast scan of the bitmap bit by bit
template <typename P_BitSet,int dim>
class EuclBitSetT<P_BitSet,dim>::BitIterator : public P_BitSet::BitIterator{

public:
  typedef typename EuclBitSetT<P_BitSet,dim>::Word Word;
//  using EuclBitSetT<P_BitSet,dim>::BitIterator::operator bool;

  const EuclBitSetT<P_BitSet,dim>* baseEuclBitSet() const{
    return reinterpret_cast<const EuclBitSetT<P_BitSet,dim>*>(this->P_BitSet::BitIterator::itSet);
  }

  explicit BitIterator(const EuclBitSetT<P_BitSet,dim>& A_EuclBitSet):P_BitSet::BitIterator(A_EuclBitSet){}

  explicit BitIterator(const EuclBitSetT<P_BitSet,dim>& A_EuclBitSet, const WordIterator& A_wIt):P_BitSet::BitIterator(A_EuclBitSet,A_wIt){}

  BitIterator(const EuclBitSetT<P_BitSet,dim>& A_EuclBitSet,int A_wordPos,int A_bitPos):P_BitSet::BitIterator(A_EuclBitSet,A_wordPos,A_bitPos){}

  // Constructor of an image of iterator A_it in the bitmap s
  BitIterator(const EuclBitSetT<P_BitSet,dim>& A_EuclBitSet,const BitIterator& A_it):P_BitSet::BitIterator(A_EuclBitSet,A_it){}

  //intended as converter, do not make it explicit
  BitIterator(const typename P_BitSet::BitIterator& A_it):P_BitSet::BitIterator(A_it){}

  BitIterator(const EuclBitSetT& A_set,Word pos):P_BitSet::BitIterator(A_set,pos){}

  BitIterator(const EuclBitSetT& A_set,const int coord[]):P_BitSet::BitIterator(A_set){
    int wordPos=coord[dim-1];
    for(int i=dim-2;i>=1;--i){
      wordPos*=A_set.wordWidth[i];
      wordPos+=coord[i];
    }
    wordPos*=A_set.wordWidth[0];
    wordPos+=coord[0]/P_BitSet::bitsPerWord;
    int bitPos=coord[0]%P_BitSet::bitsPerWord;
    BitIterator internal(A_set,wordPos,bitPos);
    std::swap(*this,internal);
  }
/*  collides with the previous constructor - why?
  template<typename P_CubSetIndex>
  BitIterator(const P_BitSet& A_set,const P_CubSetIndex& A_index): P_BitSet::BitIterator(A_set,A_index){}
*/
  BitIterator(const P_BitSet& A_set,const CubFaceIndex& A_index): P_BitSet::BitIterator(A_set,A_index){}

/*
  BitIterator(const EuclBitSetT& A_set,const Pixel& p):P_BitSet::BitIterator(A_set){
    int pos=position(A_set,p.coord);
    BitIterator internal(A_set,pos);
    std::swap(*this,internal);
  }
*/
  BitIterator(const EuclBitSetT& A_set,const Pixel& p):P_BitSet::BitIterator(A_set){
    BitIterator internal(A_set,p.coord);
    std::swap(*this,internal);
  }

/*
  BitIterator& operator=(bool b){
    P_BitSet::BitIterator::operator=(b);
    return *this;
  }
*/

  void decInDir(int i){
    if(i==0){
      P_BitSet::BitIterator::operator--();
    }else{
      this->wIt -= this->baseEuclBitSet()->wordStride[i];
    }
  }

  void incInDir(int i){
    if(i==0){
      P_BitSet::BitIterator::operator++();
    }else{
      this->wIt += this->baseEuclBitSet()->wordStride[i];
    }
  }

  void getCoords(int* coord) const{
    int pos=this->wIt - this->baseEuclBitSet()->bitmap;
    for(int i=0;i<dim;++i){
      coord[i]=pos % this->baseEuclBitSet()->wordWidth[i];
      pos /= this->baseEuclBitSet()->wordWidth[i];
    }
    coord[0]*=bitsPerWord;
    coord[0]+=this->bit;
  }

  friend std::ostream& operator<<(std::ostream& out,const BitIterator& A_it){
    int coords[dim];
    A_it.getCoords(coords);
    out << "BitIt at(" << coords[0];
    for(int i=1;i<dim;++i) out << "," << coords[i];
    out << ")";
    return out;
  }

};

#endif // _EUCLBITSET_BITITERATOR_H_
/// @}

