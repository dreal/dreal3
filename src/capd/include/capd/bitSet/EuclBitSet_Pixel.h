/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file EuclBitSet_Pixel.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_EUCLBITSET_PIXEL_H_)
#define _EUCLBITSET_PIXEL_H_

template <typename P_BitSet,int dim>
struct EuclBitSetT<P_BitSet,dim>::Pixel{
  int coord[dim];
  Pixel();
  explicit Pixel(const int* cPtr);
  explicit Pixel(const EuclBitSetT<P_BitSet,dim>::BitIterator& it);
};

template <typename P_BitSet,int dim>
inline EuclBitSetT<P_BitSet,dim>::Pixel::Pixel(){
  for(int i=0;i<dim;++i) coord[i]=0;
}

template <typename P_BitSet,int dim>
inline EuclBitSetT<P_BitSet,dim>::Pixel::Pixel(const int* cPtr){
  for(int i=0;i<dim;++i) coord[i]=cPtr[i];
}

template <typename P_BitSet,int dim>
inline EuclBitSetT<P_BitSet,dim>::Pixel::Pixel(const EuclBitSetT::BitIterator& it){
  it.getCoords(coord);
}

template <typename P_BitSet,int dim>
inline std::ostream& operator<<(std::ostream& out,const typename EuclBitSetT<P_BitSet,dim>::Pixel& p){
  out << "Pix(" << p.coord[0];
  for(int i=1;i<dim;++i) out << "," << p.coord[i];
  out << ")";
  return out;
}

// I do not understand why the above template is not found so the following specialized  functions must be added

inline std::ostream& operator<<(std::ostream& out,const EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,2>::Pixel& p){
  out << "Pix(" << p.coord[0];
  for(int i=1;i<2;++i) out << "," << p.coord[i];
  out << ")";
  return out;
}

inline std::ostream& operator<<(std::ostream& out,const EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,3>::Pixel& p){
  out << "Pix(" << p.coord[0];
  for(int i=1;i<3;++i) out << "," << p.coord[i];
  out << ")";
  return out;
}

inline std::ostream& operator<<(std::ostream& out,const EuclBitSetT<BitSetT<BitmapT<unsigned long int> >,4>::Pixel& p){
  out << "Pix(" << p.coord[0];
  for(int i=1;i<4;++i) out << "," << p.coord[i];
  out << ")";
  return out;
}


#endif

/// @}

