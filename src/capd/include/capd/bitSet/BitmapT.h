/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BitmapT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#ifndef _CAPD_BITSET_BITMAPT_H_
#define _CAPD_BITSET_BITMAPT_H_

#include "capd/auxil/memSize.h"
#include "capd/auxil/logtwo.h"
#include <string>
#include <exception>
#include <stdexcept>
#include <sstream>
#include <iostream>

template <typename word>
class BitmapT;

template <typename word>
class BitmapT{
protected:
  static const word oneMask = 1U;
  static const int bitsPerWord=sizeof(word)*8;
  static const int bitsShift=logtwo<bitsPerWord>::value;
  static const word bitsMask=(oneMask << bitsShift) -1;
//  unsigned int length;        // length in words (paddedBitWidth/bitsPerWord)
  unsigned long int length;        // length in words (paddedBitWidth/bitsPerWord)
  word* bitmap;               // pointer to the bitmap storing the set
  word* bitmapEnd;            // pointer to the first field beyond the bitmap (bitmapEnd=bitmap+length;)

  void setupBitmapMem();

public:
  typedef word Word;
  class BitIterator;

  typedef word* WordIterator;
  BitIterator begin() const;
  BitIterator end() const;

  explicit BitmapT(int A_wordLength=0, bool A_clear=false);  // BitmapT with A_wordLength words
  explicit BitmapT(int A_wordLength, const char* bytes); // BitmapT with A_wordLength words, using a provided contents
  explicit BitmapT(const std::string& s);   // Bitmap constructed from a string
  BitmapT(const BitmapT& org, bool A_clear=false);
  ~BitmapT(){
    if(bitmap){
      // -- MM  long int mem=memSize();                                                 // *** DEBUG *** //
      // -- MM  std::cout << " BitmapT~ before  memory available " << mem << std::endl; // *** DEBUG *** //
      delete[] bitmap;
      // -- MM  std::cout << "Bitmap of " << length << " bytes freed" << std::endl; // *** DEBUG *** //
      // -- MM  mem=memSize();                                                 // *** DEBUG *** //
      // -- MM  std::cout << " BitmapT~ after  memory available " << mem << std::endl; // *** DEBUG *** //
    }
  }

  const word* getBitmap() const{ return bitmap; }

  BitmapT& invert();
  BitmapT& clear();

  BitmapT& operator=(const BitmapT& A_BitMap2);
  BitmapT& operator*=(const BitmapT& A_BitMap2);
  BitmapT& operator+=(const BitmapT& A_BitMap2);
  BitmapT& operator-=(const BitmapT& A_BitMap2);
  bool operator==(const BitmapT& A_BitMap2);
  bool operator<=(const BitmapT& A_BitMap2);
  bool empty() const;
  void swapBits();
  void swapBytes();
  unsigned long int Length(){return length;}

  int getBit(word);
  void setBit(word);
  void clearBit(word);
  void changeBit(word);

  friend class BitIterator;

  friend void swap(BitmapT& A_BitMap1,BitmapT& A_BitMap2){
    std::swap(A_BitMap1.length,A_BitMap2.length);
    std::swap(A_BitMap1.bitmap,A_BitMap2.bitmap);
    std::swap(A_BitMap1.bitmapEnd,A_BitMap2.bitmapEnd);
  }
};

#include "capd/bitSet/Bitmap_BitIterator.h"

/************************************************************************************/

template <typename word>
inline typename BitmapT<word>::BitIterator BitmapT<word>::begin() const{
  return BitIterator(*this);
}

/************************************************************************************/

template <typename word>
inline typename BitmapT<word>::BitIterator BitmapT<word>::end() const{
  BitIterator internalIt(*this);
  internalIt.wIt=bitmapEnd;
  return internalIt;
}

/************************************************************************************/

template <typename word>
std::ostream& operator<<(std::ostream&,const BitmapT<word>&);

/************************************************************************************/

template <typename word>
std::istream& operator>>(std::istream&,BitmapT<word>&);

/************************************************************************************/

template <typename word>
inline int BitmapT<word>::getBit(word index){
  return ( bitmap[index >> bitsShift] >> (index & bitsMask) ) & oneMask;
}

/************************************************************************************/

template <typename word>
inline void BitmapT<word>::setBit(word index){
  bitmap[index >> bitsShift] |= (oneMask << (index & bitsMask) );
}

/************************************************************************************/

template <typename word>
inline void BitmapT<word>::clearBit(word index){
  bitmap[index >> bitsShift] &= ~(oneMask << (index & bitsMask) );
}

/************************************************************************************/

template <typename word>
inline void BitmapT<word>::changeBit(word index){
  bitmap[index >> bitsShift] ^= (oneMask << (index & bitsMask) );
}

#endif // _CAPD_BITSET_BITMAPT_H_

/// @}

