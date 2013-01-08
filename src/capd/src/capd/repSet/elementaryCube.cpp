/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file elementaryCube.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/repSet/ElementaryCube.h"

std::istream& operator>>(std::istream& inp,ElementaryInterval& A_ei){
  char ch;
  int coord,coord2;
  inp >> ch;
  if(ch!='[') throw std::ios_base::failure("ElementaryInterval::operator>>: Failed to read \'[\'");
  inp >> coord;
  inp >> ch;
  if(ch!=',' && ch!=']') throw std::ios_base::failure("ElementaryInterval::operator>>: Failed to read \',\' or \']\'");
  if(ch==','){
    inp >> coord2;
    if(!(coord2==coord || coord2==coord+1)) throw std::ios_base::failure("ElementaryInterval::operator>>: Non elementary interval found");
    inp >> ch;
  }else{
    coord2=coord;
  }
  if(ch!=']') throw std::ios_base::failure("ElementaryInterval::operator>>: Failed to read \']\'");
  if(inp.eof()) throw std::ios_base::failure("EOF encountered when reading a vector");
  A_ei.m_intervalCode=coord+coord2;  // ==2*coord+(coord2-coord);
  return inp;
}

std::ostream& operator<<(std::ostream& out,const ElementaryInterval& A_ei){
  out << "[" << A_ei.coordinate() << "," << A_ei.coordinate()+(int)A_ei.nonDegenerate() << "]";
  return out;
}

ElementaryCube::ElementaryCube(const std::vector<int>& A_c):embeddingDim(A_c.size()){
  coord = new ElementaryInterval[embeddingDim];
  for(int i=0;i<embeddingDim;++i) coord[i]=ElementaryInterval(A_c[i],true);
}

ElementaryCube::ElementaryCube(const int* A_c,int A_dim):embeddingDim(A_dim){
  coord = new ElementaryInterval[embeddingDim];
  for(int i=0;i<A_dim;++i) coord[i]=ElementaryInterval(A_c[i],true);
}

ElementaryCube::ElementaryCube(const int* A_c,const bool* A_b,int A_dim):embeddingDim(A_dim){
  coord = new ElementaryInterval[embeddingDim];
  for(int i=0;i<A_dim;++i) coord[i]=ElementaryInterval(A_c[i],A_b[i]);
}

ElementaryCube::ElementaryCube(const ElementaryCube& A_ec):embeddingDim(A_ec.embeddingDim){
  coord = new ElementaryInterval[embeddingDim];
  for(int i=0;i<embeddingDim;++i) coord[i].m_intervalCode=A_ec.coord[i].m_intervalCode;
}

// construct the j-th left or right face
ElementaryCube::ElementaryCube(const ElementaryCube& A_ec,int j,bool right):embeddingDim(A_ec.embeddingDim){
  coord = new ElementaryInterval[embeddingDim];
  for(int i=0;i<embeddingDim;++i) coord[i]=A_ec.coord[i];
  coord[j]=(
    right ?
    ElementaryInterval(coord[j].coordinate()+1,false) :  // right face
    ElementaryInterval(coord[j].coordinate(),false)      // left face
  );
}

int ElementaryCube::dimension() const{
  int d=0;
  for(int i=0;i<embeddingDimension();++i){
    d+=(int)coord[i].nonDegenerate();
  }
  return d;
}

bool ElementaryCube::operator<(const ElementaryCube& A_ec2) const{
  for(int i=0;i<embeddingDim;++i){
    if(coord[i].m_intervalCode < A_ec2.coord[i].m_intervalCode) return true;
    if(coord[i].m_intervalCode > A_ec2.coord[i].m_intervalCode) return false;
  }
  return false;
}

void ElementaryCube::primaryFaces(std::vector<ElementaryCube>& A_primaryFaces) const{
  for(int i=0;i<embeddingDim;++i){
    if(coord[i].nonDegenerate()){
      A_primaryFaces.push_back(ElementaryCube(*this,i,false));
      A_primaryFaces.push_back(ElementaryCube(*this,i,true));
    }
  }
}
void ElementaryCube::boundary(std::map<ElementaryCube,int>& A_boundary) const{
  int sgn=1;
  for(int i=0;i<embeddingDim;++i){
    if(coord[i].nonDegenerate()){
      A_boundary.insert(std::make_pair(ElementaryCube(*this,i,false),-sgn));
      A_boundary.insert(std::make_pair(ElementaryCube(*this,i,true),sgn));
      sgn=-sgn;
    }
  }
}

std::istream& operator>>(std::istream& inp,ElementaryCube& A_cu){
  std::vector<ElementaryInterval> v;
  do{
    ElementaryInterval c;
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
  A_cu.coord = new ElementaryInterval[A_cu.embeddingDim];
  for(int i=0;i<A_cu.embeddingDim;++i) A_cu.coord[i]=v[i];
  return inp;
}

std::ostream& operator<<(std::ostream& out,const ElementaryCube& A_cu){
  out << A_cu.coord[0];
  for(int i=1;i<A_cu.embeddingDim;++i) out << "x" << A_cu.coord[i];
  return out;
}

/// @}

