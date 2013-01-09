/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_PointIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_EUCLBITSET_POINTITERATOR_H_)
#define _EUCLBITSET_POINTITERATOR_H_

/*=======================================================================*/
// PointIterator is a BitSetT iterator
// intended for fast scan of the sets point after point

template <typename P_BitSet,int dim>
class EuclBitSetT<P_BitSet,dim>::PointIterator : public EuclBitSetT<P_BitSet,dim>::BitIterator{
//  friend class BitSetT<P_Bitmap>;
public:
  typedef typename EuclBitSetT<P_BitSet,dim>::BitIterator BitIterator;
  explicit PointIterator(const EuclBitSetT<P_BitSet,dim>& s):BitIterator(s){
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

