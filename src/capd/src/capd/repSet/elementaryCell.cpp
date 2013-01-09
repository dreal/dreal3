/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file elementaryCell.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/repSet/ElementaryCell.h"

// -------------------------------------------------------------------------------------- //

ElementaryCell::ElementaryCell(const int A_c[],int A_dim):embeddingDim(A_dim){
  coord = new ElementaryOneDimCell[embeddingDim];
  for(int i=0;i<A_dim;++i){
    coord[i]=ElementaryOneDimCell(A_c[i]);
  }
}

// -------------------------------------------------------------------------------------- //

ElementaryCell::ElementaryCell(const int* A_c,const bool* A_b,int A_dim):embeddingDim(A_dim){
  coord = new ElementaryOneDimCell[embeddingDim];
  for(int i=0;i<A_dim;++i) coord[i]=ElementaryOneDimCell(A_c[i],A_b[i]);
}

// -------------------------------------------------------------------------------------- //

ElementaryCell::ElementaryCell(const ElementaryCell& A_ec):embeddingDim(A_ec.embeddingDim){
  coord = new ElementaryOneDimCell[embeddingDim];
  for(int i=0;i<embeddingDim;++i) coord[i].m_intervalCode=A_ec.coord[i].m_intervalCode;
}

// -------------------------------------------------------------------------------------- //

// construct the j-th left or right face
ElementaryCell::ElementaryCell(const ElementaryCell& A_ec,int j,bool right):embeddingDim(A_ec.embeddingDim){
  coord = new ElementaryOneDimCell[embeddingDim];
  for(int i=0;i<embeddingDim;++i) coord[i]=A_ec.coord[i];
  coord[j]=(
    right ?
    ElementaryOneDimCell(coord[j].coordinate()+1,false) :  // right face
    ElementaryOneDimCell(coord[j].coordinate(),false)      // left face
  );
}

// -------------------------------------------------------------------------------------- //

// construct the j-th left or right coface
inline ElementaryCell::ElementaryCell(const ElementaryCell& A_ec,bool right,int j):embeddingDim(A_ec.embeddingDim){
  coord = new ElementaryOneDimCell[embeddingDim];
  for(int i=0;i<embeddingDim;++i) coord[i]=A_ec.coord[i];
  coord[j]=(
    right ?
    ElementaryOneDimCell(coord[j].coordinate(),true) :      // right coface
    ElementaryOneDimCell(coord[j].coordinate()-1,true)      // left coface
  );
}

// -------------------------------------------------------------------------------------- //

//int ElementaryCell::ownDim() const{
int ElementaryCell::dimension() const{
  int d=0;
  for(int i=0;i<embDim();++i){
    d+=(int)coord[i].nonDegenerate();
  }
  return d;
}

// -------------------------------------------------------------------------------------- //

bool ElementaryCell::operator<(const ElementaryCell& A_ec2) const{
  for(int i=0;i<embeddingDim;++i){
    if(coord[i].m_intervalCode < A_ec2.coord[i].m_intervalCode) return true;
    if(coord[i].m_intervalCode > A_ec2.coord[i].m_intervalCode) return false;
  }
  return false;
}

// -------------------------------------------------------------------------------------- //

void ElementaryCell::primaryFaces(std::vector<ElementaryCell>& A_primaryFaces) const{
  for(int i=0;i<embeddingDim;++i){
    if(coord[i].nonDegenerate()){
      A_primaryFaces.push_back(ElementaryCell(*this,i,false));
      A_primaryFaces.push_back(ElementaryCell(*this,i,true));
    }
  }
}

// -------------------------------------------------------------------------------------- //

void ElementaryCell::boundary(std::map<ElementaryCell,int>& A_boundary) const{
  int sgn=1;
  for(int i=0;i<embeddingDim;++i){
    if(coord[i].nonDegenerate()){
      A_boundary.insert(std::make_pair(ElementaryCell(*this,i,false),-sgn));  // left face with -sgn
      A_boundary.insert(std::make_pair(ElementaryCell(*this,i,true),sgn));    // right face with sgn
      sgn=-sgn;
    }
  }
}

// -------------------------------------------------------------------------------------- //

void ElementaryCell::coBoundary(std::map<ElementaryCell,int>& A_coBoundary) const{
  int sgn=1;
  for(int i=0;i<embeddingDim;++i){
    if(coord[i].nonDegenerate()){ // in the nondegenerate dimensions we only change sign
      sgn=-sgn;
    }else{ // in the degenerate dimensions we construct cofaces and signs are reverse as in the case of boundary
      A_coBoundary.insert(std::make_pair(ElementaryCell(*this,false,i),sgn)); // left face with sgn
      A_coBoundary.insert(std::make_pair(ElementaryCell(*this,true,i),-sgn)); // right face with -sgn
    }
  }
}

// -------------------------------------------------------------------------------------- //

ElementaryCell& ElementaryCell::operator=(const ElementaryCell& A_ec){
  if(coord) delete[] coord;
  embeddingDim=A_ec.embeddingDim;
  coord = new ElementaryOneDimCell[embeddingDim];
  for(int i=0;i<embeddingDim;++i) coord[i].m_intervalCode=A_ec.coord[i].m_intervalCode;
  return *this;
}

// -------------------------------------------------------------------------------------- //

std::istream& operator>>(std::istream& inp,ElementaryCell& A_cu){
  std::vector<ElementaryOneDimCell> v;
  do{
    ElementaryOneDimCell c;
    inp >> c;
    v.push_back(c);
    char ch(' ');
    inp >> ch;
    if(inp.eof())break;
    if(ch!='x'){
      inp.putback(ch);
      break;
    }
  }while(true);

  A_cu.embeddingDim=v.size();
  if(A_cu.coord) delete[] A_cu.coord;
  A_cu.coord = new ElementaryOneDimCell[A_cu.embeddingDim];
  for(int i=0;i<A_cu.embeddingDim;++i) A_cu.coord[i]=v[i];
  return inp;
}

// -------------------------------------------------------------------------------------- //

std::ostream& operator<<(std::ostream& out,const ElementaryCell& A_cu){
  out << A_cu.coord[0];
  for(int i=1;i<A_cu.embeddingDim;++i) out << "x" << A_cu.coord[i];
  return out;
}

// -------------------------------------------------------------------------------------- //

std::istream& operator>>(std::istream& inp,ElementaryOneDimCell& A_ei){
  char ch,firstBracket;
  int coord,coord2;
  inp >> ch;
  if(ch!='[' && ch!='(') throw std::ios_base::failure("ElementaryOneDimCell::operator>>: Failed to read \'[\' or \'(\'");
  firstBracket=ch;
  inp >> coord;
  inp >> ch;
  if(ch!=',' && ch!=']') throw std::ios_base::failure("ElementaryOneDimCell::operator>>: Failed to read \',\'");
  if(ch==','){
    inp >> coord2;
    if(!(coord2==coord || coord2==coord+1)) throw std::ios_base::failure("ElementaryOneDimCell::operator>>: Non elementary interval found");
    if(firstBracket=='[' && coord2!=coord) throw std::ios_base::failure("ElementaryOneDimCell::operator>>: \'[\' followed by a nondegenerate cell found");
    if(firstBracket=='(' && coord2!=coord+1) throw std::ios_base::failure("ElementaryOneDimCell::operator>>: \'(\' followed by a degenerate cell found");
    inp >> ch;
  }else{
    coord2=coord;
  }
  if(ch!=']' && ch!=')') throw std::ios_base::failure("ElementaryOneDimCell::operator>>: Failed to read \']\' or \')\'");
  if(inp.eof()) throw std::ios_base::failure("EOF encountered when reading a vector");
  A_ei.m_intervalCode=coord+coord2;  // ==2*coord+(coord2-coord);
  return inp;
}

// -------------------------------------------------------------------------------------- //

std::ostream& operator<<(std::ostream& out,const ElementaryOneDimCell& A_ei){
  if(A_ei.nonDegenerate()){
    out << "(" << A_ei.coordinate() << "," << A_ei.coordinate()+1 << ")";
  }else{
    out << "[" << A_ei.coordinate() << "," << A_ei.coordinate() << "]";
  }
  return out;
}

// -------------------------------------------------------------------------------------- //

/// @}

