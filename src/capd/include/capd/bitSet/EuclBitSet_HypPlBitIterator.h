/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_HypPlBitIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_EUCLBITSET_HYPPLBITITERATOR_H_)
#define _EUCLBITSET_HYPPLBITITERATOR_H_


template <typename P_BitSet,int dim>
class EuclBitSetT<P_BitSet,dim>::HypPlBitIterator : public EuclBitSetT<P_BitSet,dim>::BitIterator{

public:

  // Hyperplane H(c):={(x_1,x_2,...,x_d) | c_i>=0  ==> x_i==c_i}
  // (negative coordinates serve as wildcards)
  //
  explicit HypPlBitIterator(const EuclBitSetT<P_BitSet,dim>& A_EuclBitSet,int A_coord[]):
    EuclBitSetT<P_BitSet,dim>::BitIterator(A_EuclBitSet)
  {
    int c[dim];
    for(int i=0;i<dim;++i){
      coord[i] = ( A_coord[i]<0 ? 0 : -1 );
      c[i] = ( A_coord[i]<0 ? 0 : A_coord[i] );
    }
    typename EuclBitSetT<P_BitSet,dim>::BitIterator bi(*this->baseEuclBitSet(),c);
    this->wIt=bi.wIt;
    this->bit=bi.bit;
  }

  void operator++(){
    for(int i=0;i<dim;++i){
      if(coord[i]<0) continue;
      ++coord[i];
      if(coord[i]<this->baseEuclBitSet()->getPaddedWidth(i)){
        if(i==0){
          this->operator++();
        }else{
          this->wIt += this->baseEuclBitSet()->wordStride[i];
        }
        return;
      }else{
        coord[i]=0;
        if(i==0){
          this->operator-=(this->baseEuclBitSet()->getPaddedWidth(0)-1);
        }else{
          this->wIt -= (this->baseEuclBitSet()->getPaddedWidth(i)-1) * this->baseEuclBitSet()->wordStride[i];
        }
      }
    }
    // When there is no break from the loop, we reached the end of hyperplane
    // We mark it by setting the iterator at the end of the whole bitmap
    this->wIt=this->baseEuclBitSet()->end().wIt;
    this->bit=this->baseEuclBitSet()->end().bit;
  }

  void nextWord(){
    for(int i=0;i<dim;++i){
      if(coord[i]<0) continue;
      if(i!=0){
        ++coord[i];
      }else{
        coord[i]+=EuclBitSetT<P_BitSet,dim>::bitsPerWord;
      }
      if(coord[i]<this->baseEuclBitSet()->getPaddedWidth(i)){
        this->wIt += this->baseEuclBitSet()->wordStride[i];
        return;
      }else{
        coord[i]=0;
        this->wIt -= (this->baseEuclBitSet()->wordWidth[i]-1) * this->baseEuclBitSet()->wordStride[i];
      }
    }
    // When there is no break from the loop, we reached the end of hyperplane
    // We mark it by setting the iterator at the end of the whole bitmap
    this->wIt=this->baseEuclBitSet()->end().wIt;
    this->bit=this->baseEuclBitSet()->end().bit;
  }

private:
  int coord[dim];
};

#endif // _EUCLBITSET_HYPPLBITITERATOR_H_
/// @}

