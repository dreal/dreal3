/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CubFaceIndex.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 



#if !defined(_CUB_FACE_INDEX_H_)
#define _CUB_FACE_INDEX_H_

#include "capd/repSet/ElementaryCell.h"

class ElementaryCell;

class CubFaceIndex{
//private:
public:
  unsigned int word;
  unsigned char bit;
public:
  CubFaceIndex():word(0),bit(0){}

  template<typename Iterator>
  CubFaceIndex(const Iterator& A_it):
  word(A_it.wIt-A_it.itSet->begin()),
  bit(A_it.bit)
  {}

  template<typename P_set>
  CubFaceIndex(const P_set& A_set,const ElementaryCell& A_cell){
    typename P_set::BitCoordIterator it(A_set,A_cell.coords());
    word=it.wIt-it.A_set->begin();
    bit=it.bit;
  }

  friend bool operator<(const CubFaceIndex& A_cfi1,const CubFaceIndex& A_cfi2){
    if(A_cfi1.word != A_cfi2.word) return A_cfi1.word < A_cfi2.word;
    else return A_cfi1.bit < A_cfi2.bit;
  }
  friend std::ostream& operator<<(std::ostream& out,const CubFaceIndex& A_cfi){
    out << "CFI[" << A_cfi.word << ":" << A_cfi.bit << "]";
    return out;
  }
};


#endif //_CUB_FACE_INDEX_H_
