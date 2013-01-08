/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file elementaryCell.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_ELEMENTARYCELL_H_)
#define _ELEMENTARYCELL_H_

#include <iostream>
#include <sstream>
#include <vector>
#include <map>
//#include "bitSet/CubFaceIndex.h"


class CubFaceIndex;
class ElementaryCell;

// ********** class ElementaryOneDimCell ********** //
/*
  The class ElementaryOneDimCell is used to store intervals [k,k] and (k,k+1),
  i.e. one dimensional cells. It is an auxiliary class for class ElementaryCell below.
*/
class ElementaryOneDimCell{
public:
  ElementaryOneDimCell(){}
  ElementaryOneDimCell(int A_code):m_intervalCode(A_code){}
  ElementaryOneDimCell(int A_coord,bool nondegenerate):m_intervalCode(2*A_coord+(int)nondegenerate){}
  ElementaryOneDimCell(const char* c){
    std::istringstream s(c);
    s >> *this;
  }
  bool nonDegenerate() const{ return bool(m_intervalCode%2);}
  int coordinate() const{
    return (m_intervalCode-nonDegenerate())/2;
  }
  friend std::istream& operator>>(std::istream& inp,ElementaryOneDimCell& A_ei);
  friend std::ostream& operator<<(std::ostream& out,const ElementaryOneDimCell& A_ei);
  friend class ElementaryCell;
private:
  int m_intervalCode;  // m_intervalCode=2*leftEnd+size,
                       // which means odd value 2*k+1 denotes a nondegenerate elementary interval (k,k+1)
                       // and even value 2*k denotes a degenerate elementary interval [k,k]
};// ********** class ElementaryOneDimCell ********** //




// ********** class ElementaryCell ********** //
/*
This class is used to store elementry cells as described in
    M. Mrozek, K. Mischaikow and T. Kaczynski,
    Computational Homology,
    Applied Mathematical Sciences 157, Springer-Verlag, New York, 2004
*/
class ElementaryCell{
public:
  ElementaryCell():embeddingDim(0),coord(0){}
  // Warning, this constructor is a temporary, unsafe shortcut
  // It shoud be replaced by a constructor which takes as argument a vector
  // of elements of class CellCoordCode(to be written)
  ElementaryCell(const int A_c[],int A_dim);
  ElementaryCell(const int* A_c,const bool* A_b,int A_dim);
  ElementaryCell(const ElementaryCell& A_ec);
  // construct the j-th left or right face
  ElementaryCell(const ElementaryCell& A_ec,int j,bool right);
  // construct the j-th left or right coface (Note: it differs from the above constructor only by the order of arguments)
  ElementaryCell(const ElementaryCell& A_ec,bool right,int j);
  ElementaryCell(const char* c):embeddingDim(0),coord(0){
    std::istringstream s(c);
    s >> *this;
  }

  template<typename P_set>
  ElementaryCell(const P_set& A_set,const CubFaceIndex& A_index){
    typename P_set::BitCoordIterator it(A_set,A_index);
    embeddingDim=it.embDim();
    coord = new ElementaryOneDimCell[embeddingDim];
    for(int i=0;i<embeddingDim;++i){
      coord[i]=it[i];
    }
  }
  template<typename P_iterator>
  ElementaryCell(const P_iterator& A_iterator){
    embeddingDim=A_iterator.embDim();
    coord = new ElementaryOneDimCell[embeddingDim];
    for(int i=0;i<embeddingDim;++i){
      coord[i]=A_iterator[i];
    }
  }
  ~ElementaryCell(){
    if(coord) delete[] coord;
  }

  bool nonDegenerate(int i) const{
    return coord[i].nonDegenerate();
  }

  int leftCoordinate(int i) const{
    return coord[i].coordinate();
  }

  int rightCoordinate(int i) const{
    return coord[i].coordinate()+(int)coord[i].nonDegenerate();
  }

  ElementaryCell& operator=(const ElementaryCell& A_ec);
  int embDim() const{return embeddingDim;}
  int ownDim() const{ return dimension();}
  int embeddingDimension() const{return embeddingDim;}  // obsolete
  int dimension() const;                                // obsolete
  bool operator<(const ElementaryCell& A_ec2) const;
  void primaryFaces(std::vector<ElementaryCell>& A_primaryFaces) const;
  void boundary(std::map<ElementaryCell,int>& A_boundary) const;
  void coBoundary(std::map<ElementaryCell,int>& A_coBoundary) const;
  const int* coords() const{
    return reinterpret_cast<int *>(coord);
  }
  friend std::istream& operator>>(std::istream& inp,ElementaryCell& A_cu);
  friend std::ostream& operator<<(std::ostream& out,const ElementaryCell& A_cu);
private:
  int embeddingDim;
  ElementaryOneDimCell *coord;
};// ********** class ElementaryCell ********** //

#endif //_ELEMENTARYCELL_H_
/// @}

