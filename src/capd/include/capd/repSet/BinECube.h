/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BinECube.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/*
    Class template: BinECube
    (c) Marian Mrozek, Kraków 2004

    The objects of this class represent
    an elementary full cube.
    It is assumed that the cube is one of the cubes obtained
    in the process of binary subdividing of a given root cube

    Template parameters:
      SCALAR
        - type used to represent real numbers
      BINCODE
        - integer type used to store the binary code of the location
          of the elementary cube
      DIM
        - dimension of the space in which the cubes are embedded

    Object data:
      code
        - a binary code representing the location of the elementary
          cube in the binary tree coming from the process of
          subdividing the root cube.
          Significant are the last depth*DIM bits
          The code is a concatenation of the coordinates
          in the set {0,1,2,...,2^depth-1} represented by depth bits
          in every dimension, so together is depth*DIM bits
      depth
        - an integer showing on which level of subdivision of the root
          cube the given cube resides


    Object methods:
      botCoords
        - returns the lower coordinates of the elementary cube
      size
        - returns the size in each dimension
      operator<
        - lexicographical comparision of the location of the two cubes

    Nested classes:
      BinBaseInterval
        - used to translate between the SCALAR coordinates and their
          uint counterparts from {0,1,2,...,2^depth-1} in one dimension
      BinBaseCube
        - used to declare coordinates of the base cube and the depth of
          division for each axis.
*/

#ifndef _CAPD_REPSET_BINECUBE_H_ 
#define _CAPD_REPSET_BINECUBE_H_ 
#include <vector>
#include <iostream>
#include <sstream>
#include <string>
#include <stdexcept>
#include "capd/interval/DoubleInterval.h"
#include "vectalg/vectorMD_Intf.h"

typedef unsigned int uint;

/*
-----------------------
Class Template BinECube
-----------------------
*/

template<typename SCALAR, typename BINCODE, uint DIM>
class BinECube{
public:
  class BinBaseCube;
  typedef SCALAR Scalar ;
  typedef BINCODE BinCode;
  static uint const Dim=DIM;
  static SCALAR rootBotCoords[DIM],rootSize[DIM];

  explicit BinECube():
    code(0), baseCubePtr(0){};
  explicit BinECube(BINCODE const& a_code, BinBaseCube const* a_baseCubePtr):
    code(a_code),baseCubePtr(a_baseCubePtr){};
  explicit BinECube(std::vector<uint> const& positions, BinBaseCube const* a_baseCubePtr);

  std::string toString() const;
  // covering interval vector
  operator Vector<interval,0>() const;
  // a cube from subdivision by two indicated by code c
  BinECube subCube(uint c) const;
  // vector of integer position codes for each coordinate
  std::vector<uint> unpack() const;
  // table of short position codes for each coordinate (for CHomP program)
  void unpack(short int* c) const;
  // the 3^d neighbors through codimension one face
  std::vector<BinECube<SCALAR,BINCODE,DIM> > neighbors() const;
  // vector of the coordinates of the vertex with minimal coordinates
  std::vector<SCALAR> botCoords() const;
  // vector of sizes in each dimension
  std::vector<SCALAR> size() const;
  // read only acces to code
  BinCode getCode() const;
  // bitwise comparision
  bool operator<(BinECube const& ec) const;
  // embedding dimension
  int embeddingDimension() const{return DIM;}

private:
  struct BinBaseInterval;
  BINCODE code;
  const BinBaseCube* baseCubePtr;
};

/*
-----------------------
Nested Class Template BinBaseInterval
-----------------------
*/

template<typename SCALAR, typename BINCODE, uint DIM>
struct BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval{
  SCALAR left,right;
  SCALAR length;     // equals right-left;
  uint depth,numberOfElementaryIntervals;  //equals 2^depth
  SCALAR lengthOfElementaryInterval; //equals length/numberOfElementaryIntervals
public:
  void initialize(SCALAR a_left,SCALAR a_right,uint a_depth);
  BinBaseInterval(){};
  BinBaseInterval(SCALAR a_left,SCALAR a_right,uint a_depth);
  int leftPosition(SCALAR x) const;  // negative value means no position found
  int rightPosition(SCALAR x) const; // negative value means no position found
  SCALAR leftEnd(uint pos) const;
  SCALAR rightEnd(uint pos) const;
  uint leftHalf(uint pos) const;
  uint rightHalf(uint pos) const;
  uint mask() const;
};

/*
-----------------------
Nested Class Template BinBaseCube
-----------------------
*/

template<typename SCALAR, typename BINCODE, uint DIM>
class BinECube<SCALAR,BINCODE,DIM>::BinBaseCube{
  BinBaseInterval axis[DIM];
  BinBaseCube* subdividedPtr;
public:
  friend class  BinECube<SCALAR,BINCODE,DIM>;
  BinBaseCube(){};
  BinBaseCube(SCALAR const& bot, SCALAR const& top, uint a_depth);
  BinBaseCube(std::vector<SCALAR> const& bot, std::vector<SCALAR> const& top, std::vector<uint> const& a_depth);
  explicit BinBaseCube(Vector<interval,0> iv, uint a_depth);
  const BinBaseInterval& getAxis(int i) const{ return axis[i];}
  void subdivide();
  BinBaseCube& subdivided();
  ~BinBaseCube();
};

/*
--------------------------------
Class Template BinECube: methods
--------------------------------
*/

template<typename SCALAR, typename BINCODE, uint DIM>
BinECube<SCALAR,BINCODE,DIM>::
BinECube(std::vector<uint> const& position, BinBaseCube const* a_baseCubePtr):
  code(0),baseCubePtr(a_baseCubePtr){
  for(int i=DIM-1;i>=0;i--){
    code <<= baseCubePtr->axis[i].depth;
    code |= position[i];
  }
}

template<typename SCALAR, typename BINCODE, uint DIM>
std::string
BinECube<SCALAR,BINCODE,DIM>::
toString() const{
  std::ostringstream result;
  std::vector<uint> b=unpack();
  for(uint i=0;i<DIM-1;i++) result << b[i] << "-";
  result << b[DIM-1];
  return result.str();
}

template<typename SCALAR, typename BINCODE, uint DIM>
typename BinECube<SCALAR,BINCODE,DIM>::BinECube
BinECube<SCALAR,BINCODE,DIM>::
subCube(uint c) const{
  std::vector<uint> b=unpack();
  std::vector<uint> bNew;
  bNew.reserve(DIM);
  for(uint i=0;i<DIM;i++){
    bNew[i]=(
      c & 1 ?
      baseCubePtr->axis[i].rightHalf(b[i]):
      baseCubePtr->axis[i].leftHalf(b[i])
    );
    c >>= 1;
  }
  if(!baseCubePtr->subdividedPtr){
    // --> Rethink if this const_cast can be avoided
    BinBaseCube* bbc=const_cast<BinBaseCube*>(baseCubePtr);
    bbc->subdivide();
  }
  BinECube& bec=*new BinECube(bNew,baseCubePtr->subdividedPtr);
  return bec;
}

template<typename SCALAR, typename BINCODE, uint DIM>
BinECube<SCALAR,BINCODE,DIM>::
operator Vector<interval,0>() const{
  Vector<interval,0> result(DIM);
  std::vector<SCALAR> bc=botCoords();
  std::vector<SCALAR> sz=size();
  for(uint i=0;i<DIM;i++){
    result[i]=interval(bc[i],bc[i]+sz[i]);
  }
  return result;
}

template<typename SCALAR, typename BINCODE, uint DIM>
std::vector<uint>
BinECube<SCALAR,BINCODE,DIM>::
unpack() const{
  std::vector<uint> result;
  result.reserve(DIM);
  BINCODE codeCopy=code;
  for(uint i=0;i<DIM;i++){
    result[i]=codeCopy & baseCubePtr->axis[i].mask();
    codeCopy >>= baseCubePtr->axis[i].depth;
  }
  return result;
}

template<typename SCALAR, typename BINCODE, uint DIM>
void
BinECube<SCALAR,BINCODE,DIM>::
unpack(short int* c) const{
  BINCODE codeCopy=code;
  for(uint i=0;i<DIM;i++){
    c[i]=codeCopy & baseCubePtr->axis[i].mask();
    codeCopy >>= baseCubePtr->axis[i].depth;
  }
}

/*

// Ta metoda wyznacza jedynie s¹siadów "przez œcianê",
// ale ju¿ nie "przez krawêdŸ", czy "przez wierzcho³ek"

template<typename SCALAR, typename BINCODE, uint DIM>
std::vector<BinECube<SCALAR,BINCODE,DIM> >
BinECube<SCALAR,BINCODE,DIM>::
neighbors() const{
  std::vector<BinECube> result;
  std::vector<uint> positions=unpack();
  for(int i=0;i<DIM;i++){
    if(positions[i]>0){
      positions[i]--;
      result.push_back(BinECube<SCALAR,BINCODE,DIM>(positions,baseCubePtr));
      positions[i]++;
    }
    if(positions[i]<baseCubePtr->axis[i].numberOfElementaryIntervals-1){
      positions[i]++;
      result.push_back(BinECube<SCALAR,BINCODE,DIM>(positions,baseCubePtr));
      positions[i]--;
    }
  }
  return result;
}
*/

template<typename SCALAR, typename BINCODE, uint DIM>
std::vector<BinECube<SCALAR,BINCODE,DIM> >
BinECube<SCALAR,BINCODE,DIM>::
neighbors() const{
  std::vector<BinECube> result;
  std::vector<uint> positions(unpack());
//  For some reason the copy constructor in vector has problems with this line
//  std::vector<uint> posMin(positions);
//  std::vector<uint> posMax(positions);
  std::vector<uint> posMin(unpack());
  std::vector<uint> posMax(unpack());

  for(int i=0;i<(int)DIM;i++){
    if(positions[i]>0) positions[i]--;
    if(posMin[i]>0) posMin[i]--;
    if(posMax[i]<baseCubePtr->axis[i].numberOfElementaryIntervals-1){
      posMax[i]++;
    }
  }
  while(true){
    result.push_back(BinECube<SCALAR,BINCODE,DIM>(positions,baseCubePtr));
    for(int i=0;i<(int)DIM;i++){
      positions[i]++;
      if(positions[i]<=posMax[i]) break;
      if(i==DIM-1) return result;
      positions[i]=posMin[i];
    }
  }
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline BINCODE
BinECube<SCALAR,BINCODE,DIM>::
getCode() const{
  return code;
}

template<typename SCALAR, typename BINCODE, uint DIM>
std::vector<SCALAR>
BinECube<SCALAR,BINCODE,DIM>::
botCoords() const{
  std::vector<SCALAR> v;
  v.reserve(DIM);
  std::vector<uint> b=unpack();

  for(int i=0;i<(int)DIM;i++){
    v[i]=baseCubePtr->axis[i].leftEnd(b[i]);
  }
  return v;
}

template<typename SCALAR, typename BINCODE, uint DIM>
std::vector<SCALAR>
BinECube<SCALAR,BINCODE,DIM>::
size() const{
  std::vector<SCALAR> v;
  v.reserve(DIM);
  for(int i=0;i<(int)DIM;i++){
    v[i]=baseCubePtr->axis[i].lengthOfElementaryInterval;
  }
  return v;
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline bool
BinECube<SCALAR,BINCODE,DIM>::
operator<(BinECube<SCALAR,BINCODE,DIM> const& ec) const{
  return code < ec.code;
}

/*
-----------------------
Class Template BinBaseInterval: Methods
-----------------------
*/

template<typename SCALAR, typename BINCODE, uint DIM>
inline void
BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
initialize(SCALAR a_left,SCALAR a_right,uint a_depth){
  left=a_left;
  right=a_right;
  depth=a_depth;
  length=right-left;
  numberOfElementaryIntervals= (1 << depth);
  lengthOfElementaryInterval=length/numberOfElementaryIntervals;
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
BinBaseInterval(SCALAR a_left,SCALAR a_right,uint a_depth):
  left(a_left),right(a_right),depth(a_depth){
  length=right-left;
  numberOfElementaryIntervals= (1 << depth);
  lengthOfElementaryInterval=length/numberOfElementaryIntervals;
}

template<typename SCALAR, typename BINCODE, uint DIM>
int
BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
leftPosition(SCALAR x) const{
  SCALAR l(left),r(right);
  int position=0;
  for(uint i=0;i<depth;i++){
    position <<= 1;
    SCALAR mid=(l+r)/2;
    if(x<=mid){
      r=mid;
    }else{
      l=mid;
      position |= 1;
    }
  }
  return position;
}

template<typename SCALAR, typename BINCODE, uint DIM>
int
BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
rightPosition(SCALAR x) const{
  SCALAR l(left),r(right);
  int position=0;
  for(uint i=0;i<depth;i++){
    position <<= 1;
    SCALAR mid=(l+r)/2;
    if(x<mid){
      r=mid;
    }else{
      l=mid;
      position |= 1;
    }
  }
  return position;
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline SCALAR
BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
leftEnd(uint pos) const{
  return left+pos*lengthOfElementaryInterval;
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline SCALAR
BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
rightEnd(uint pos) const{
  return left+(pos+1)*lengthOfElementaryInterval;
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline uint
BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
leftHalf(uint pos) const{
  return 2*pos;
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline uint
BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
rightHalf(uint pos) const{
  return 2*pos+1;
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline uint
BinECube<SCALAR,BINCODE,DIM>::BinBaseInterval::
mask() const{
  return (1<<depth)-1;
}
/*
-----------------------
Class Template BinBaseCube: Methods
-----------------------
*/

template<typename SCALAR, typename BINCODE, uint DIM>
BinECube<SCALAR,BINCODE,DIM>::BinBaseCube::
BinBaseCube(SCALAR const& bot, SCALAR const& top, uint a_depth):
  subdividedPtr(0){
  for(uint i=0;i<DIM;i++){
    axis[i].initialize(bot,top,a_depth);
  }
}


template<typename SCALAR, typename BINCODE, uint DIM>
BinECube<SCALAR,BINCODE,DIM>::BinBaseCube::
BinBaseCube(std::vector<SCALAR> const& bot, std::vector<SCALAR> const& top, std::vector<uint>  const& a_depth):
  subdividedPtr(0){
  for(uint i=0;i<DIM;i++){
    axis[i].initialize(bot[i],top[i],a_depth[i]);
  }
}

template<typename SCALAR, typename BINCODE, uint DIM>
BinECube<SCALAR,BINCODE,DIM>::BinBaseCube::
BinBaseCube(Vector<interval,0> iv, uint a_depth):
  subdividedPtr(0){
  for(uint i=0;i<DIM;i++){
    axis[i].initialize(iv[i].leftBound(),iv[i].rightBound(),a_depth);
  }
}

template<typename SCALAR, typename BINCODE, uint DIM>
void
BinECube<SCALAR,BINCODE,DIM>::BinBaseCube::
subdivide(){
  if(!subdividedPtr){
    std::vector<uint> newDepth;
    std::vector<SCALAR> newBot;
    std::vector<SCALAR> newTop;
    newDepth.reserve(DIM);
    newBot.reserve(DIM);
    newTop.reserve(DIM);
    for(uint i=0;i<DIM;i++){
      newDepth[i]=axis[i].depth+1;
      newBot[i]=axis[i].left;
      newTop[i]=axis[i].right;
    }
    subdividedPtr=new BinBaseCube(newBot,newTop,newDepth);
  }else{
    throw std::out_of_range("BinECube<SCALAR,BINCODE,DIM>::BinBaseCube::subdivide:  already subdivided.");
  }
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline typename BinECube<SCALAR,BINCODE,DIM>::BinBaseCube&
BinECube<SCALAR,BINCODE,DIM>::BinBaseCube::
subdivided(){
  return *subdividedPtr;
}

template<typename SCALAR, typename BINCODE, uint DIM>
inline
BinECube<SCALAR,BINCODE,DIM>::BinBaseCube::
~BinBaseCube(){
  if(subdividedPtr) delete subdividedPtr;
}

#endif // _CAPD_REPSET_BINECUBE_H_ 
/// @}

