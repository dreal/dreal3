/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_BitCoordIterator.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

/*=======================================================================*/
// BitCoordIterator is a general use iterator for bitmap sets
// It behaves similarly to the BitIterator but
// unlike the previous operators it stores and updates the
// cooridnates of the pixel

#if !defined(_EUCLBITSETT_BITCOORDITERATOR_H_)
#define _EUCLBITSETT_BITCOORDITERATOR_H_

template <typename P_BitSet,int dim>
class EuclBitSetT<P_BitSet,dim>::BitCoordIterator : public EuclBitSetT<P_BitSet,dim>::BitIterator{
  typedef typename EuclBitSetT<P_BitSet,dim>::BitIterator BitIterator;
  typedef typename EuclBitSetT<P_BitSet,dim>::Word Word;
  friend class EuclBitSetT<P_BitSet,dim>;
protected:
  static const int bitsPerWord = 8*sizeof(typename EuclBitSetT<P_BitSet,dim>::Word);
  int coord[dim];

  bool incCoord(){
    for(int k=0;k<dim;++k){
      if(++coord[k]<this->baseEuclBitSet()->paddedBitWidth[k]) return true;
      coord[k]=0;
    }
    return false;
  }

  bool decCoord(){
    for(int k=0;k<dim;++k){
      if(--coord[k]>=0) return true;
      coord[k]=this->baseEuclBitSet()->paddedBitWidth[k]-1;
    }
    return false;
  }

  bool incCoord(int n){ // increase by n
    for(int k=0;k<dim;++k){
      if( (this->coord[k]+=n) < this->baseEuclBitSet()->paddedBitWidth[k] ) return true;
      n = this->coord[k] / this->baseEuclBitSet()->paddedBitWidth[k];
      this->coord[k] %= this->baseEuclBitSet()->paddedBitWidth[k];
    }
    return false;
  }

public:

  bool findPoint(){
    Word* c=this->wIt;
    int b=this->bit;
    this->BitIterator::findPoint();
    int n=(this->wIt - c)*bitsPerWord + (this->bit - b);
    this->incCoord(n);
    return this->wIt < this->baseEuclBitSet()->bitmapEnd;
  }

  BitCoordIterator(const EuclBitSetT& s):BitIterator(s){
    for(int k=0;k<dim;++k) coord[k]=0;
  }

  // Constructor of an image of iterator A_it in the bitmap s
  BitCoordIterator(const EuclBitSetT& s,const BitCoordIterator& A_it):
    BitIterator(s,A_it)
  {
    for(int i=0;i<dim;++i) coord[i]=A_it.coord[i];
  }

  BitCoordIterator(const EuclBitSetT& s,const int* A_coord):BitIterator(s,A_coord){
    for(int k=0;k<dim;++k) coord[k]=A_coord[k];
  }

  BitCoordIterator(const EuclBitSetT& s,const Pixel& p):BitIterator(s,p){
    for(int k=0;k<dim;++k) coord[k]=p.coord[k];
  }

  BitCoordIterator(const EuclBitSetT& s, Word pos):BitIterator(s,pos){
    for(int i=0;i<dim;++i){
      coord[i]=pos % s.getPaddedWidth(i);
      pos /= s.getPaddedWidth(i);
    }
  }

  // intended as a converter
  BitCoordIterator(const BitIterator& A_it): BitIterator(A_it){
    int pos=this->wIt - this->baseEuclBitSet()->getBitmap();
    for(int i=0;i<dim;++i){
      coord[i]=pos % this->baseEuclBitSet()->wordWidth[i];
      pos /= this->baseEuclBitSet()->wordWidth[i];
    }
    coord[0]*=bitsPerWord;
    coord[0]+=this->bit;
  }

  // intended as a converter
/*
  BitCoordIterator(const BitParIterator& A_it): BitIterator(A_it){
    int pos=this->wIt - this->baseEuclBitSet()->getBitmap();
    for(int i=0;i<dim;++i){
      coord[i]=pos % this->baseEuclBitSet()->wordWidth[i];
      pos /= this->baseEuclBitSet()->wordWidth[i];
    }
    coord[0]*=bitsPerWord;
    coord[0]+=this->bit;
  }
*/

  // intended as a converter
/*
  BitCoordIterator(const PointParIterator& A_it): BitIterator(A_it){
    int pos=this->wIt - this->baseEuclBitSet()->getBitmap();
    for(int i=0;i<dim;++i){
      coord[i]=pos % this->baseEuclBitSet()->wordWidth[i];
      pos /= this->baseEuclBitSet()->wordWidth[i];
    }
    coord[0]*=bitsPerWord;
    coord[0]+=this->bit;
  }
*/

  template<typename P_CubSetIndex>
  BitCoordIterator(const EuclBitSetT& A_set,const P_CubSetIndex& A_index): BitIterator(A_set,A_index){
    int pos=this->wIt - this->baseEuclBitSet()->getBitmap();
    for(int i=0;i<dim;++i){
      coord[i]=pos % this->baseEuclBitSet()->wordWidth[i];
      pos /= this->baseEuclBitSet()->wordWidth[i];
    }
    coord[0]*=bitsPerWord;
    coord[0]+=this->bit;
  }

  bool odd(int i){
    return coord[i] & 1;
  }

  BitCoordIterator& decInDir(int i){
    coord[i]--;
    if(i==0){
      BitIterator::operator--();
    }else{
      this->wIt -= this->baseEuclBitSet()->wordStride[i];
    }
    return *this;
  }

  BitCoordIterator& incInDir(int i){
    coord[i]++; // this must be so, do not put here incCoord(), we want to know that we moved out of bounds!
    if(i==0){
      BitIterator::operator++();
    }else{
      this->wIt += this->baseEuclBitSet()->wordStride[i];
    }
    return *this;
  }

  BitCoordIterator& operator++(){
    BitIterator::operator++();
    incCoord();
    return *this;
  }

  BitCoordIterator& operator--(){
    BitIterator::operator--();
    decCoord();
    return *this;
  }

  int operator[](int j) const{
    return coord[j];
  }

  const int* coords() const{
    return coord;
  }

  // This function computes the number of odd coordinates
  // of the iterator and should be called simply dim, not embDim
  // It seems that it is used only in CubCellSetT<P_EuclSet>::shaveBCI()
/*
  int embDim(){
    int d=0;
    for(int i=0;i<dim;++i) d+= (this->coord[i] & 1);
    return d;
  }
*/
  int ownDim() const{
    int d=0;
    for(int i=0;i<dim;++i) d+= (this->coord[i] & 1);
    return d;
  }
  int embDim() const{
    return dim;
  }

  Pixel operator*(){
    return Pixel(coords());
  }

  // for efficiency reasons bitmaps are padded to 32 bits in dim=0
  // This function answers if the iterator points inside the actual, not the physical space
  bool inSpace(){
    return coord[0] < this->baseEuclBitSet()->actualDimZeroBitWidth;
  }

  std::string toString(){
    std::ostringstream s;
    s << "BitCooordIter for bitmap at " << this->baseEuclBitSet() << " with wIt=" << this->wIt << " bit=" << this->bit << " at pixel " << *this << std::endl;
    return s.str();
  }

  friend std::ostream& operator<<(std::ostream& out,const BitCoordIterator& A_it){
//    if(A_it){
      out << "BitCoordIt at(" << A_it[0];
      for(int i=1;i<dim;++i) out << "," << A_it[i];
      out << ")[" << A_it.position() << "]" ;
//    }else{
//      out << "BitCoordIt at none";
//    }
    return out;
  }

};
#endif //_EUCLBITSETT_BITCOORDITERATOR_H_

/*=======================================================================*/
/// @}

