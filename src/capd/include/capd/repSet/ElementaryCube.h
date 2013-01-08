/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file elementaryCube.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#if !defined(_ELEMENTARYCUBE_H_)
#define _ELEMENTARYCUBE_H_
#include <iostream>
#include <sstream>
#include <vector>
#include <map>

class ElementaryCube;

// ********** class ElementaryInterval ********** //
/*
  The class ElementaryInterval is used to store elementary intervals of the form [k,k] and [k,k+1],
  It is an auxiliary class for class ElementaryCube below.
*/
class ElementaryInterval{
public:
  ElementaryInterval(){}
  ElementaryInterval(int A_coord,bool nondegenerate=false):m_intervalCode(2*A_coord+(int)nondegenerate){}
  ElementaryInterval(const char* c){
    std::istringstream s(c);
    s >> *this;
  }
  bool nonDegenerate() const{ return bool(m_intervalCode%2);}
  int coordinate() const{
    return (m_intervalCode-nonDegenerate())/2;
  }
  friend std::istream& operator>>(std::istream& inp,ElementaryInterval& A_ei);
  friend std::ostream& operator<<(std::ostream& out,const ElementaryInterval& A_ei);
  friend class ElementaryCube;
private:
  int m_intervalCode;  // m_intervalCode=2*leftEnd+size,
                       // which means odd value 2*k+1 denotes a nondegenerae elementary interval [k,k+1]
                       // and even value 2*k denotes a degenerate elementary interval [k,k]
};// ********** class ElementaryInterval ********** //




// ********** class ElementaryCube ********** //
/*
This class is used to store elementry cubes as described in
    M. Mrozek, K. Mischaikow and T. Kaczynski,
    Computational Homology,
    Applied Mathematical Sciences 157, Springer-Verlag, New York, 2004
*/
class ElementaryCube{
public:
  ElementaryCube():embeddingDim(0),coord(0){}

  ElementaryCube(const std::vector<int>& A_c);
  ElementaryCube(const int* A_c,int A_dim);
  ElementaryCube(const int* A_c,const bool* A_b,int A_dim);
  ElementaryCube(const ElementaryCube& A_ec);
  // construct the j-th left or right face
  ElementaryCube(const ElementaryCube& A_ec,int j,bool right);
  ElementaryCube(const char* c):embeddingDim(0),coord(0){
    std::istringstream s(c);
    s >> *this;
  }

  ~ElementaryCube(){
    if(coord) delete[] coord;
  }

  int coordinateCode(int i) const{
    return coord[i].m_intervalCode;
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

  int embeddingDimension() const{
    return embeddingDim;
  }

  int dimension() const;
  bool operator<(const ElementaryCube& A_ec2) const;
  void primaryFaces(std::vector<ElementaryCube>& A_primaryFaces) const;
  void boundary(std::map<ElementaryCube,int>& A_boundary) const;

  friend std::istream& operator>>(std::istream& inp,ElementaryCube& A_cu);
  friend std::ostream& operator<<(std::ostream& out,const ElementaryCube& A_cu);

private:
  int embeddingDim;
  ElementaryInterval *coord;
};// ********** class ElementaryCube ********** //
#endif // _ELEMENTARYCUBE_H_
/// @}

