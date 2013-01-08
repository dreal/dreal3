/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSetPixelNeighborOffset.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_BMPCUBSETPIXELNEIGHBOROFFSET_H_)
#define _BMPCUBSETPIXELNEIGHBOROFFSET_H_

template <typename P_BitSet,int dim>
struct EuclBitSetT<P_BitSet,dim>::PixelNeighborOffset{
  int offset[dim];
  static PixelNeighborOffset bottom(){
    PixelNeighborOffset o;
    for(int i=0;i<dim;++i) o.offset[i]=-1;
    return o;
  }
  static PixelNeighborOffset top(){
    PixelNeighborOffset o;
    for(int i=0;i<dim;++i) o.offset[i]=1;
    return o;
  }
  bool operator==(const PixelNeighborOffset& o2) const{
    for(int i=0;i<dim;++i) if(offset[i]!=o2.offset[i]) return false;
    return true;
  }
  PixelNeighborOffset& operator++(){
    for(int i=0;i<dim;++i){
      ++offset[i];
      if(offset[i]<=1) break;
      else offset[i]=-1;
    }
    return *this;
  }
};
#endif //_BMPCUBSETPIXELNEIGHBOROFFSET_H_



/// @}

