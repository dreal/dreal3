/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_PointCoordIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*=======================================================================*/
// PointCoordIterator is a general use PointCoordIterator for bitmap sets
// It behaves similarly to the PointIterator but
// unlike the previous operators it stores and updates the
// cooridnates of the point

#if !defined(_EUCLBITSETT_POINTCOORDITERATOR_H_)
#define _EUCLBITSETT_POINTCOORDITERATOR_H_

template <typename P_BitSet,int dim>
class EuclBitSetT<P_BitSet,dim>::PointCoordIterator : public EuclBitSetT<P_BitSet,dim>::BitCoordIterator{
  friend class EuclBitSetT<P_BitSet,dim>;

protected:

  static const int bitsPerWord = 8*sizeof(typename EuclBitSetT<P_BitSet,dim>::Word);


public:

  PointCoordIterator(const EuclBitSetT& s):BitCoordIterator(s){

    for(int k=0;k<dim;k++) this->coord[k]=0;
    this->findPoint();
  }

  // intended as a converter
  PointCoordIterator(const BitIterator& A_it): BitCoordIterator(A_it){
    this->findPoint();
  }

  PointCoordIterator(const BitCoordIterator& A_it): BitCoordIterator(A_it){}

  // Keep it here! Do not inherit
  PointCoordIterator& operator++(){
    EuclBitSetT<P_BitSet,dim>::BitIterator::operator++();
    this->EuclBitSetT::BitCoordIterator::incCoord();
    this->findPoint();
    return *this;
  }

};
#endif //_EUCLBITSETT_POINTCOORDITERATOR_H_

/*=======================================================================*/
/// @}

