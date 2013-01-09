/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ECell3dCode.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_ECELL3DCODE_H_)
#define _ECELL3DCODE_H_

#include <iostream>
#include <sstream>
#include <vector>
#include <map>
#include "capd/repSet/ElementaryCell.h"


// ********** class ECell3dCode ********** //
/*
This class is used to code 3d elementry cells as described in
    M. Mrozek, K. Mischaikow and T. Kaczynski,
    Computational Homology,
    Applied Mathematical Sciences 157, Springer-Verlag, New York, 2004
*/
class ECell3dCode{
private:
  static const unsigned int embeddingDim=3;
  static const unsigned int bitsPerDimension=8*sizeof(unsigned int)/embeddingDim;
  static const unsigned int bitsPerDimensionDoubled=2*bitsPerDimension;
  static const unsigned long int unit=1;
  static const unsigned long int mask0=0x3ff;
  static const unsigned long int mask1=0x3ff << bitsPerDimension;
  static const unsigned long int mask2=0x3ff << bitsPerDimensionDoubled;
public:
  ECell3dCode():m_code(0){}
  // Warning, this constructor is a temporary, unsafe shortcut
  // It shoud be replaced by a constructor which takes as argument a vector
  // of elements of class CellCoordCode(to be written)
  ECell3dCode(const int A_c[],int);
  ECell3dCode(const ElementaryCell&  A_c);
  ECell3dCode(const int* A_c,const bool* A_b,int A_dim);

  // construct the j-th left or right face
  ECell3dCode(const ECell3dCode& A_ec,int j,bool right);
  // construct the j-th left or right coface (Note: it differs from the above constructor only by the order of arguments)
  ECell3dCode(const ECell3dCode& A_ec,bool right,int j);
  ECell3dCode(const char* c):m_code(0){
    std::istringstream s(c);
    s >> *this;
  }

  template<typename P_Set>
  ECell3dCode(const P_Set&,const ECell3dCode& A_ec):m_code(A_ec.m_code){}

  template<typename P_iterator>
  explicit ECell3dCode(const P_iterator& A_iterator):m_code(0){
    for(unsigned int i=0;i<embeddingDim;++i){
      setValAtCoord(i,A_iterator[i]);
    }
  }

  unsigned int getValAtCoord(int i) const{
    switch(i){
      case 0:  return m_code & mask0;
      case 1:  return (m_code >> bitsPerDimension) & mask0;
      case 2:  return (m_code >> bitsPerDimensionDoubled) & mask0;
      default: return 0;
    }
  }

  bool nonDegenerateAtCoord(int i) const{
    switch(i){
      case 0:  return bool(m_code & unit);
      case 1:  return bool((m_code >> bitsPerDimension) &  unit);
      case 2:  return bool((m_code >> bitsPerDimensionDoubled) &  unit);
      default: return false;
    }
  }

  void setValAtCoord(int i,unsigned int val){
    switch(i){
      case 0: (m_code &= ~mask0) |= val; return;
      case 1: (m_code &= ~mask1) |= (val << bitsPerDimension); return;
      case 2: (m_code &= ~mask2) |= (val << bitsPerDimensionDoubled); return;
      default:;
    }
  }



  int embDim() const{return embeddingDim;}
  int ownDim() const;
  bool operator<(const ECell3dCode A_ec2) const{
    return m_code < A_ec2.m_code;
  }
/*
  bool operator<(const ECell3dCode& A_ec2) const{
    return m_code < A_ec2.m_code;
  }
*/
  void primaryFaces(std::vector<ECell3dCode>& A_primaryFaces) const;
  void boundary(std::map<ECell3dCode,int>& A_boundary) const;
  void coBoundary(std::map<ECell3dCode,int>& A_coBoundary) const;

/*
  friend bool operator==(const ECell3dCode& A_a,const ECell3dCode& A_b){
    return A_a.m_code==A_b.m_code;
  }
  friend bool operator!=(const ECell3dCode& A_a,const ECell3dCode& A_b){
    return A_a.m_code!=A_b.m_code;
  }
*/
  friend bool operator==(const ECell3dCode A_a,const ECell3dCode A_b){
    return A_a.m_code==A_b.m_code;
  }
  friend bool operator!=(const ECell3dCode A_a,const ECell3dCode A_b){
    return A_a.m_code!=A_b.m_code;
  }

  friend std::istream& operator>>(std::istream& inp,ECell3dCode& A_cu);
  friend std::ostream& operator<<(std::ostream& out,const ECell3dCode& A_cu);
private:
  unsigned long int m_code;
};// ********** class ECell3dCode ********** //


// -------------------------------------------------------------------------------------- //

inline ECell3dCode::ECell3dCode(const int A_c[],int):m_code(0){
  setValAtCoord(0,A_c[0]);
  setValAtCoord(1,A_c[1]);
  setValAtCoord(2,A_c[2]);
}

inline ECell3dCode::ECell3dCode(const ElementaryCell& A_c):m_code(0){
  setValAtCoord(0,A_c.coords()[0]);
  setValAtCoord(1,A_c.coords()[1]);
  setValAtCoord(2,A_c.coords()[2]);
}

// -------------------------------------------------------------------------------------- //
// Note: in this representation the code for faces and cofaces (below) is the same
inline ECell3dCode::ECell3dCode(const ECell3dCode& A_ec,int j,bool right):m_code(A_ec.m_code){
  if(right){
    switch(j){
      case 0:  m_code+=unit; break;
      case 1:  m_code+=(unit << bitsPerDimension); break;
      case 2:  m_code+=(unit << bitsPerDimensionDoubled); break;
      default:;
    }
  }else{
    switch(j){
      case 0:  m_code -= unit; break;
      case 1:  m_code -= (unit << bitsPerDimension); break;
      case 2:  m_code -= (unit << bitsPerDimensionDoubled); break;
      default:;
    }
  }
}


// -------------------------------------------------------------------------------------- //

inline ECell3dCode::ECell3dCode(const ECell3dCode& A_ec,bool right,int j):m_code(A_ec.m_code){
  if(right){
    switch(j){
      case 0:  m_code+=unit; return;
      case 1:  m_code+=(unit << bitsPerDimension); return;
      case 2:  m_code+=(unit << bitsPerDimensionDoubled); return;
      default:;
    }
  }else{
    switch(j){
      case 0:  m_code -= unit; return;
      case 1:  m_code -= (unit << bitsPerDimension); return;
      case 2:  m_code -= (unit << bitsPerDimensionDoubled); return;
      default:;
    }
  }
}

// -------------------------------------------------------------------------------------- //

inline int ECell3dCode::ownDim() const{
  int d=0;
  for(unsigned int i=0;i<embeddingDim;++i){
    if(nonDegenerateAtCoord(i)) ++d;
  }
  return d;
}

// -------------------------------------------------------------------------------------- //

inline void ECell3dCode::primaryFaces(std::vector<ECell3dCode>& A_primaryFaces) const{
  for(unsigned int i=0;i<embeddingDim;++i){
    if(nonDegenerateAtCoord(i)){
      A_primaryFaces.push_back(ECell3dCode(*this,i,false));
      A_primaryFaces.push_back(ECell3dCode(*this,i,true));
    }
  }
}

// -------------------------------------------------------------------------------------- //

inline void ECell3dCode::boundary(std::map<ECell3dCode,int>& A_boundary) const{
  int sgn=1;
  for(unsigned int i=0;i<embeddingDim;++i){
    if(nonDegenerateAtCoord(i)){
      A_boundary.insert(std::make_pair(ECell3dCode(*this,i,false),-sgn));  // left face with -sgn
      A_boundary.insert(std::make_pair(ECell3dCode(*this,i,true),sgn));    // right face with sgn
      sgn=-sgn;
    }
  }
}

// -------------------------------------------------------------------------------------- //

inline void ECell3dCode::coBoundary(std::map<ECell3dCode,int>& A_coBoundary) const{
  int sgn=1;
  for(unsigned int i=0;i<embeddingDim;++i){
    if(nonDegenerateAtCoord(i)){ // in the nondegenerate dimensions we only change sign
      sgn=-sgn;
    }else{ // in the degenerate dimensions we construct cofaces and signs are reverse as in the case of boundary
      A_coBoundary.insert(std::make_pair(ECell3dCode(*this,false,i),sgn)); // left face with sgn
      A_coBoundary.insert(std::make_pair(ECell3dCode(*this,true,i),-sgn)); // right face with -sgn
    }
  }
}

// -------------------------------------------------------------------------------------- //

inline std::ostream& operator<<(std::ostream& out,const ECell3dCode& A_cu){
  for(unsigned int i=0;i<A_cu.embeddingDim;++i){
    int j=A_cu.getValAtCoord(i);
    int k=j/2;
    if(i) out << "x";
    if(j & A_cu.unit){
      out << "(" << k << "," << k+1 << ")";
    }else{
      out << "[" << k << "]";
    }
  }
//-- out << "{" << hex << A_cu.m_code << dec << "}";
  return out;
}

// -------------------------------------------------------------------------------------- //

inline std::istream& operator>>(std::istream& inp,ECell3dCode& A_cu){
  ElementaryCell ec;
  inp >> ec;
  A_cu.m_code=0;
  A_cu.setValAtCoord(0,ec.coords()[0]);
  A_cu.setValAtCoord(1,ec.coords()[1]);
  A_cu.setValAtCoord(2,ec.coords()[2]);
  return inp;
}

// -------------------------------------------------------------------------------------- //

#endif //_ECELL3DCODE_H_
/// @}

