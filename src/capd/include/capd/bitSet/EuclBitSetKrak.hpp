/// @addtogroup matrixAlgorithms
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSetKrak.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_EUCLBITSETT_KRAK_HPP_)
#define _EUCLBITSETT_KRAK_HPP_

template <typename P_BitSet,int dim>
inline void showBmpCubSet(const EuclBitSetT<P_BitSet,dim>& set,int color,bool clear,bool rescale=true){
  int scale=1;
  if(rescale) scale=krakHeight/set.paddedBitWidth[1];
  if(scale<1) scale=1;
  int io=2;
  int jo=(krakWidth-scale*set.actualDimZeroBitWidth)/2;
  if(jo<1) jo=1;
  Frame f(jo,io,scale*set.actualDimZeroBitWidth+jo,scale*set.paddedBitWidth[1]+io);
  if(clear) f.Clear();
  f.Bound();
  rootFrame << At(0,0) << "card is " << set.cardinality();


  typename EuclBitSetT<P_BitSet,dim>::PointCoordIterator it(set);

  for(it=set.begin();it<set.end();++it){
    int i=set.paddedBitWidth[1]-1-it[1];
    int j=it[0];
    if(j<set.actualDimZeroBitWidth){
      if(scale>1){
        f.boxFill(jo+scale*j,io+scale*i,jo+scale*(j+1),io+scale*(i+1),color);
      }else{
        f.dot(jo+j,io+i,color);
      }
    }
  }
}


template <typename P_BitSet,int dim>
void showBmpCubSet(const EuclBitSetT<P_BitSet,dim>& set,int color=BLUE,bool clear=true){
  showBmpCubSet<P_BitSet,dim>(set,color,clear,true);
}

#endif //_EUCLBITSETT_KRAK_HPP_


/// @}

