/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file Bitmap_BitIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_BITMAP_BITITERATOR_H_)
#define _BITMAP_BITITERATOR_H_

#include "capd/bitSet/CubFaceIndex.h"
#include "capd/auxil/logtwo.h"

/*=======================================================================*/
// BitIterator is a BitmapT iterator
// intended for fast scan of the bitmap bit by bit
template <typename word>
class BitmapT<word>::BitIterator{
  friend class BitmapT<word>;
  friend class CubFaceIndex;
//protected:
public:
  typedef typename BitmapT<word>::WordIterator WordIterator;
  static const int bitsPerWord = 8*sizeof(word);
  static const int bitsShift=logtwo<bitsPerWord>::value;
  static const word startingMask = 1U;
  static const word oneMask = 1U;
  static const word bitsMask=(oneMask << bitsShift) -1;
  WordIterator wIt;
  int bit;
  const BitmapT<word>* itSet;

/*
  // set iterator to none when b is fale
  // otherwise set it to the beginning of the bitmap
  BitIterator& operator=(bool b){
    if(!b){
      wIt=itSet->bitmapEnd;
    }else{
      wIt=itSet->bitmap;
      bit=0;
    }
    return *this;
  }
*/

  void nextBit(){
    ++bit;
  }

  void prevBit(){
    --bit;
  }

  void nextBit(int n){
    bit+=n;
  }

  void prevBit(int n){
    bit-=n;
  }

public:

  explicit BitIterator(const BitmapT<word>& A_Bitmap):wIt(A_Bitmap.bitmap),bit(0),itSet(&A_Bitmap){}

  explicit BitIterator(const BitmapT<word>& A_Bitmap, const WordIterator& A_wIt):wIt(A_wIt),bit(0),itSet(&A_Bitmap){}

  BitIterator(const BitmapT<word>& A_Bitmap,const CubFaceIndex& A_index):wIt(A_Bitmap.bitmap+A_index.word),bit(A_index.bit),itSet(&A_Bitmap){}

  BitIterator(const BitmapT<word>& A_Bitmap,int A_wordPos,int A_bitPos):
    wIt(A_Bitmap.bitmap+A_wordPos),bit(A_bitPos),itSet(&A_Bitmap){
  }

  BitIterator(const BitmapT<word>& A_Bitmap,word A_pos):
    wIt(A_Bitmap.bitmap+A_pos/bitsPerWord),bit(A_pos & bitsMask),itSet(&A_Bitmap){
  }

  // Constructor of the image of iterator A_it in the bitmap s
  BitIterator(const BitmapT<word>& A_Bitmap,const BitIterator& A_it):
    wIt(A_Bitmap.bitmap+(A_it.wIt-A_it.itSet->bitmap)),bit(A_it.bit),itSet(&A_Bitmap){
  }

  operator WordIterator(){ return wIt;}

  const BitmapT<word>& getBitmap() const{ return *itSet;}

  void setBit(int val){
    if(val) *wIt |= (oneMask << bit);
    else *wIt &= ~(oneMask << bit);
  }

  void setBit(){
    *wIt |= (oneMask << bit);
  }

  void changeBit(){
    *wIt ^= (oneMask << bit);
  }

  void clearBit(){
    *wIt &= ~(oneMask << bit);
  }

  int getBit() const{
    return (*wIt & (oneMask << bit)) != 0;
  }

  void operator--(){
    prevBit();
    if(bit<0){
      --wIt;
      bit=bitsPerWord-1;
    }
  }

  void operator++(){
    nextBit();
    if(bit>=bitsPerWord){
      ++wIt;
      bit=0;
    }
  }

  void operator+=(int n){
    if(n>0){
      int remainingBits=bitsPerWord-bit;
      if(n<remainingBits){
        nextBit(n);
      }else{
        ++wIt;
        bit=0;
        n-=remainingBits;
        wIt+=n/bitsPerWord;
        nextBit(n%bitsPerWord);
      }
    }else if(n<0){
      n=-n;
      if(n<=bit){
        prevBit(n);
      }else{
        n-=bit;
        bit=0;
        wIt-=n/bitsPerWord;
        if(int bitsLeft=n%bitsPerWord){
          --wIt;
          nextBit(bitsPerWord-bitsLeft);
        }
      }
    }
  }

  void operator-=(int n){
    this->operator+=(-n);
  }

  bool operator<(const BitIterator& it2) const{
    if(wIt!=it2.wIt) return wIt < it2.wIt;
    else return bit<it2.bit;
  }

  // check current bit
  // return true if nonzero
  // otherwise move iterator forward up to the first non zero bit
  // in the current word if such a bit exists and return true
  // or stop at the beginning of the next word and return false
  bool findNextPointInWord(){
    // return true if a nonzero point found in the current word
    for(;bit<bitsPerWord;nextBit()) if(getBit()) return true;
    // otherwise move to the first bit in the next word and return false
    ++wIt;
    bit=0;
    return false;
  }

  // return true if the iterator points to a nonzero bit (a Point)
  // move forward to the next point and return true if a point in a word before the end word still exists
  // otherwise return false
//  bool findPoint(const WordIterator& end_wIt){
  bool findPoint(){
    const WordIterator& end_wIt=this->itSet->bitmapEnd;
    // do not search if already beyond the bitmap
    if(wIt>=end_wIt) return false;
    // first try to find a point in the current word
    if(this->findNextPointInWord()) return true;
    // if point not found, search for the first nonzero word
    // and set the iterator as pointing to the first nonzero bit in this word
    for(
      WordIterator wIt0=wIt;
      wIt0 < end_wIt;
      ++wIt0
    ){
      if(*wIt0){
        wIt=wIt0;
        goto found;
      }
    }
    // No nonzero word found, i.e. no more points exist
    wIt=end_wIt; // ensure that the iterator itself indicates that nothing was found
    return false;         // indicate that no more points exist by returning false
    found:
    return findNextPointInWord();
  }

  int position() const{
    return (wIt-itSet->bitmap)*bitsPerWord+bit;
  }
/*
  word number() const{
    return (wIt-itSet->bitmap)*bitsPerWord+bit;
  }
*/


};

#endif // _BITMAP_BITITERATOR_H_
/// @}

