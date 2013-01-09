/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BitSet_PointIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 





#if !defined(_BITSET_POINTITERATOR_H_)
#define _BITSET_POINTITERATOR_H_

/*=======================================================================*/
// PointIterator is a BitSetT iterator
// intended for fast scan of the sets point after point

template <typename P_Bitmap>
class BitSetT<P_Bitmap>::PointIterator : public P_Bitmap::BitIterator{
  friend class BitSetT<P_Bitmap>;
public:
  typedef typename P_Bitmap::BitIterator BitIterator;
  explicit PointIterator(const BitSetT<P_Bitmap>& s):BitIterator(s){
    this->findPoint();
  }
  PointIterator(const BitIterator& A_it):BitIterator(A_it){
    this->findPoint();
  }

  PointIterator& operator++(){
    this->BitIterator::operator++();
    this->findPoint();
    return *this;
  }
};

/*=======================================================================*/

#endif
/// @}

