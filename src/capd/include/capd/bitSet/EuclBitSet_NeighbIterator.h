/// @addtogroup matrixAlgorithms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_NeighbIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_EUCLBITSETT_NEIGHBITERATOR_H_)
#define _EUCLBITSETT_NEIGHBITERATOR_H_

/*=======================================================================*/
// NeighbIterator is a EuclBitSetT iterator
// intended for scan of the neighborhood of a given point
//
// This is the specialization for <unsigned long int,2> !!!

template<>
class EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,2>::NeighbIterator : public EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,2>::BitIterator{
  friend class EuclBitSetT<unsigned long int,2>;
protected:
  unsigned int i0,i1; // values in {0,1,2} only
public:
  NeighbIterator(const EuclBitSetT& A_s, const EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,2>::BitIterator& A_it):
    EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,2>::BitIterator(A_s,A_it),i0(0),i1(0){}
  void operator++(){
    if(++i0<3){
      (*this)+=this->baseEuclBitSet()->neighbStride[0];
      return;
    }else{
      i0=0;
    }
    if(++i1<3){
      (*this)+=this->baseEuclBitSet()->neighbStride[1];
      return;
    }else{
      i1=0;
    }
    ++(*this);
  }
};

/*=======================================================================*/
// NeighbIterator is a EuclBitSetT iterator
// intended for scan of the neighborhood of a given point
//
// This is the specialization for <unsigned long int,3> !!!

template<>
class EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,3>::NeighbIterator : public EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,3>::BitIterator{
  friend class EuclBitSetT<unsigned long int,3>;
protected:
  unsigned int i0,i1,i2; // values in {0,1,2} only
public:
  NeighbIterator(const EuclBitSetT& A_s, const EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,3>::BitIterator& A_it):
    EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,3>::BitIterator(A_s,A_it),i0(0),i1(0),i2(0){}
  void operator++(){
    if(++i0<3){
      (*this)+=this->baseEuclBitSet()->neighbStride[0];
      return;
    }else{
      i0=0;
    }
    if(++i1<3){
      (*this)+=this->baseEuclBitSet()->neighbStride[1];
      return;
    }else{
      i1=0;
    }
    if(++i2<3){
      (*this)+=this->baseEuclBitSet()->neighbStride[2];
      return;
    }else{
      i2=0;
    }
    ++(*this);
  }
};

/*=======================================================================*/
// NeighbIterator is a EuclBitSetT iterator
// intended for scan of the neighborhood of a given point

template <typename P_BitSet,int dim>
class EuclBitSetT<P_BitSet,dim>::NeighbIterator : public EuclBitSetT<P_BitSet,dim>::BitIterator{
  friend class EuclBitSetT<P_BitSet,dim>;
protected:
  unsigned char locCoord[dim]; // locCoord takes values in {0,1,2} only
public:
  NeighbIterator(const EuclBitSetT& A_s, const EuclBitSetT<P_BitSet,dim>::BitIterator& A_it):
    EuclBitSetT<P_BitSet,dim>::BitIterator(A_s,A_it)
  {
    for(int i=0;i<dim;++i) locCoord[i]=0;
  }
  void operator++(){
    for(int i=0;i<dim;++i){
      if(++locCoord[i]<3){
        (*this)+=this->baseEuclBitSet()->neighbStride[i];
        return;
      }else{
        locCoord[i]=0;
      }
    }
    ++(*this); // This seems to call itself recursively. Although the result seems to be acceptable,
               // I believe the intention was to call this->BitIterator::operator++();
  }
};
#endif //_EUCLBITSETT_NEIGHBITERATOR_H_


/*=======================================================================*/
/// @}

