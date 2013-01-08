/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BitSetT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 





#ifndef _CAPD_BITSET_BITSETT_H_ 
#define _CAPD_BITSET_BITSETT_H_ 
#include <iostream>


template <typename P_Bitmap>
class BitSetT : public P_Bitmap{
protected:

public:

  using P_Bitmap::Length;
  typedef typename P_Bitmap::Word Word;
  typedef typename P_Bitmap::BitIterator BitIterator;
  typedef typename P_Bitmap::WordIterator WordIterator;
  typedef P_Bitmap BaseClass;

  class PointIterator;
  explicit BitSetT(int A_wordLength=0, bool A_clear=false):P_Bitmap(A_wordLength,A_clear){}   // BitSetT with A_wordLength words
  explicit BitSetT(int A_wordLength, const char* bytes):P_Bitmap(A_wordLength,bytes){}        // BitSetT with A_wordLength words, using a provided contents
  explicit BitSetT(const std::string& A_s):P_Bitmap(A_s){}   // BitSetT with A_wordLength words filled with data from a string
  BitSetT(const P_Bitmap& A_org, bool A_clear=false):P_Bitmap(A_org,A_clear){}
  const BaseClass& getBaseObject() const{ return *static_cast<const BaseClass*>(this);}

  friend class PointIterator;

  int cardinality() const;

  friend void swap(BitSetT& A_BitSet1,BitSetT& A_BitSet2){
    swap(static_cast<P_Bitmap &>(A_BitSet1),static_cast<P_Bitmap &>(A_BitSet2));
  }
};

/************************************************************************************/

#include "capd/bitSet/BitSet_PointIterator.h"

template <typename P_Bitmap>
inline int BitSetT<P_Bitmap>::cardinality() const{
  int cardi=0;
  PointIterator eIt=this->end();
  for(PointIterator it=this->begin();it<eIt;++it){
    ++cardi;
  }
  return cardi;
}

#endif // _CAPD_BITSET_BITSETT_H_ 

/// @}

