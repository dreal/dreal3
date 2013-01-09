/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CubSetT.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#if !defined(_TOPCUBSETT_HPP_)
#define _TOPCUBSETT_HPP_

#include <fstream>
#include <stack>
#include <list>
#include "capd/bitSet/CubSetT.h"
#include "capd/homologicalAlgebra/acyclicConfigs.h"
#include "capd/auxil/CRef.h"

/************************************************************************************/

template <typename P_EuclSet>
void CubSetT<P_EuclSet>::getNeighbors(const Pixel& p, vector<Pixel>& neighbors) const{
  PixelNeighborOffset botOffset=PixelNeighborOffset::bottom();
  PixelNeighborOffset o=PixelNeighborOffset::bottom();
  PixelNeighborOffset topOffset=PixelNeighborOffset::top();
  do{
    Pixel q;
    for(int i=0;i<this->embDim();++i) if(o.offset[i]) goto notMiddle;
    goto do_next;

    notMiddle:
    for(int i=0;i<this->embDim();++i){
      q.coord[i]=p.coord[i]+o.offset[i];
      if(q.coord[i]<0 || q.coord[i]>=this->getPaddedWidth(i)) goto do_next;
    }
    neighbors.push_back(q);
    do_next:
    ++o;
  }while(!(o==botOffset));
}

/************************************************************************************/
// NOTE: getNeighborhood3 differs from getNeighborhood5 below only by the size of
// the nieghborhood constructed: The 5 version has an additional empty collar.
// Most likely the 5 version is not needed anymore, but it is not tested everywhere
// it was used, so as long as all the tests are not performed, this 5 version should be preserved
template <typename P_EuclSet>
void CubSetT<P_EuclSet>::getNeighborhood3(const Pixel& p, CubSetT& neighborhood) const{

  PixelNeighborOffset botOffset=PixelNeighborOffset::bottom();
  PixelNeighborOffset o=PixelNeighborOffset::bottom();
  PixelNeighborOffset topOffset=PixelNeighborOffset::top();
  do{
    Pixel q;
    Pixel qq;
    for(int i=0;i<this->embDim();++i) if(o.offset[i]) goto notMiddle;
    goto do_next;

    notMiddle:
    for(int i=0;i<this->embDim();++i){
      q.coord[i]=p.coord[i]+o.offset[i];
      if(q.coord[i]<0 || q.coord[i]>=this->getUnpaddedWidth(i)) goto do_next;
    }
    if(containsPixel(q)){
      for(int d=0;d<this->embDim();++d) qq.coord[d]=q.coord[d]-p.coord[d]+1;
      neighborhood.addPixel(qq);
    }
    do_next:
    ++o;
  }while(!(o==botOffset));
}

/************************************************************************************/

template <typename P_EuclSet>
void CubSetT<P_EuclSet>::getNeighborhood5(const Pixel& p, CubSetT& neighborhood) const{

  PixelNeighborOffset botOffset=PixelNeighborOffset::bottom();
  PixelNeighborOffset o=PixelNeighborOffset::bottom();
  PixelNeighborOffset topOffset=PixelNeighborOffset::top();
  do{
    Pixel q;
    Pixel qq;
    for(int i=0;i<this->embDim();++i) if(o.offset[i]) goto notMiddle;
    goto do_next;

    notMiddle:
    for(int i=0;i<this->embDim();++i){
      q.coord[i]=p.coord[i]+o.offset[i];
      if(q.coord[i]<0 || q.coord[i]>=this->getUnpaddedWidth(i)) goto do_next;
    }
    if(containsPixel(q)){
      for(int d=0;d<this->embDim();++d) qq.coord[d]=q.coord[d]-p.coord[d]+2;
      neighborhood.addPixel(qq);
    }
    do_next:
    ++o;
  }while(!(o==botOffset));
}

/************************************************************************************/

template <typename P_EuclSet>
void CubSetT<P_EuclSet>::addEmptyCollar(){
  std::vector<int> newBitWidth(this->embDim());
  for(int i=0;i<this->embDim();++i){
    newBitWidth[i]=2+this->getUnpaddedWidth(i);
  }
  CubSetT<P_EuclSet> newCubSet(&newBitWidth[0]); // true means clear
  for(PointCoordIterator it=this->begin(); it<this->end();++it){
    Pixel p(it.coords());
    for(int i=0;i<this->embDim();++i) ++p.coord[i];
    newCubSet.addPixel(p);
  }
  swap(*this,newCubSet);
}

/************************************************************************************/

template <typename P_EuclSet>
CubSetT<P_EuclSet>& CubSetT<P_EuclSet>::expandToComponentOf(const Pixel& p, /* in */ const CubSetT<P_EuclSet>& set2){
  std::stack<Pixel> pixelsToProcess;  // this stack will store pixels whose neighborhood must be processed
  pixelsToProcess.push(p);    // we begin with the pixel found
  addPixel(p);                // add the pixel to the component
  while(!pixelsToProcess.empty()){
    // we take the pixel from the top
    Pixel p=pixelsToProcess.top();
    pixelsToProcess.pop();

    // we construct the candidates for the neighbors (some may turn out to be out of bounds of the bitmap
    vector<Pixel> neighbors;
    getNeighbors(p,neighbors);
    // we process all neighbors
    for(int k=0;k<(int)neighbors.size();++k){
      // if the neighbor is in the given set but not yet added to the component
      if(
        set2.containsPixel(neighbors[k]) != 0 &&
        containsPixel(neighbors[k]) == 0
      ){
        addPixel(neighbors[k]);    // add the pixel to the component
        pixelsToProcess.push(neighbors[k]); // push the pixel to the stack of components to process
      }
    }
  }
  return *this;
}

/************************************************************************************/

// A version which also returns lower and upper corner of the minimal enclosing box in lc and uc
template <typename P_EuclSet>
CubSetT<P_EuclSet>& CubSetT<P_EuclSet>::expandToComponentOf(const Pixel& p, /* in */ const CubSetT<P_EuclSet>& set2, Pixel& lc, Pixel& uc){
  std::stack<Pixel> pixelsToProcess;  // this stack will store pixels whose neighborhood must be processed
  pixelsToProcess.push(p);    // we begin with the pixel found
  for(int i=0;i<this->embDim();++i) lc.coord[i]=uc.coord[i]=p.coord[i];
  addPixel(p);                // add the pixel to the component
  while(!pixelsToProcess.empty()){
    // we take the pixel from the top
    Pixel p=pixelsToProcess.top();
    pixelsToProcess.pop();
    // we construct the candidates for the neighbors (some may turn out to be out of bounds of the bitmap
    vector<Pixel> neighbors;
    getNeighbors(p,neighbors);
    // we process all neighbors
    for(int k=0;k<neighbors.size();++k){
      // if the neighbor is in the given set but not yet added to the component
      if(
        set2.containsPixel(neighbors[k]) != 0 &&
        containsPixel(neighbors[k]) == 0
      ){
        addPixel(neighbors[k]);    // add the pixel to the component
        for(int i=0;i<this->embDim();++i){
          lc.coord[i]=std::min(lc.coord[i],neighbors[k].coord[i]);
          uc.coord[i]=std::max(uc.coord[i],neighbors[k].coord[i]);
        }
        pixelsToProcess.push(neighbors[k]); // push the pixel to the stack of components to process
      }
    }
  }
}

/************************************************************************************/

template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::extractComponent(CubSetT<P_EuclSet>& component,CubSetT<P_EuclSet>& rest){
  Pixel p;
  if(!findSomePoint(p)) return false;
/*
fcout << " Component length is " << component.Length() << std::endl;
fcout << " Rest length is " << rest.Length() << std::endl;
*/
  component.clear();
  component.expandToComponentOf(p,*this);
  CubSetT<P_EuclSet> restLoc(*this);
  restLoc-=component;
  rest=restLoc;
  return true;
}

/************************************************************************************/

template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::extractComponent(CubSetT<P_EuclSet>& component,CubSetT<P_EuclSet>& rest, Pixel& lc, Pixel& uc){
  Pixel p;
  if(!findSomePoint(p)) return false;

  component.clear();
  component.expandToComponentOf(p,*this,lc,uc);

  CubSetT<P_EuclSet> restLoc(*this);
  restLoc-=component;
  rest=restLoc;
  return true;
}

/************************************************************************************/

template <typename P_EuclSet>
int CubSetT<P_EuclSet>::decomposeToComponents(vector< CubSetT<P_EuclSet> >& components) const{
  CubSetT<P_EuclSet> component(*this);

  CubSetT<P_EuclSet> rest(*this);
  int numberOfComponents=0;

  while(rest.extractComponent(component,rest)){
    components.push_back(component);
    ++numberOfComponents;
  }
  return numberOfComponents;
}

/************************************************************************************/

/* This method replaces *this by the union of all connected components of set2, which
   have non-empty intersection with *this, doing it in an efficient way */
template <typename P_EuclSet>
CubSetT<P_EuclSet>& CubSetT<P_EuclSet>::expandToComponentOf(const CubSetT<P_EuclSet>& set2){
  // in org we keep the copy of the original bitmap
  const CubSetT<P_EuclSet> org(*this);
  // we start the search of the component with an empty bitmap
  this->clear();
  // the loop will be exited by return, when we find the whole component
  while(true){
    // we search for a pixel which is in the original bitmap but not yet in the constructed component
    WordIterator wiOrg,wiThis;
    for(wiOrg=org.begin(),wiThis=this->begin();wiThis<this->end();++wiOrg,++wiThis){
      if(  *wiOrg & (~(*wiThis)) ) goto found; // this word contains such a pixel
    }
    // if no such pixel is found, the construction of the component is finished
    return *this;

  found:
    // Now we want to locate precisely the pixel, so we use bit iterators
    BitIterator biOrg(org,wiOrg);
    BitIterator biThis(*this,wiThis);

    while(!(biOrg.getBit() && !biThis.getBit())){
      ++biOrg;
      ++biThis;
    }
    // Pixel is located, we add it to the set
    biThis.setBit();
    // Then we convert it to a pixel given by coordinates, and construct its
    // component in set2
    Pixel p(biThis);
    expandToComponentOf(p,set2);
  }
  return *this;
}


/************************************************************************************/
// The intersection of a set of neighbors of a pixel is defined as simple if in every
// direction the intersection of the projections on that direction is non-empty
/*   it seems to be not used anymore
template <typename P_EuclSet>
int CubSetT<P_EuclSet>::neighbSignature(const BitIterator& it) const{
  const uint midBit=int(0.5+pow(3.0,this->embDim()))/2;
  int signature=0;
  BitIterator endIt=this->neighbEnd(it);
  int pos=0;
  for(NeighbIterator nbIt=this->neighbBegin(it);nbIt<endIt;++nbIt){
    signature = signature | (nbIt.getBit() << pos++);
  }
  return signature & ~(1 << midBit);
}
*/

/************************************************************************************/
//

template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclicLT(const BitIterator& it) const{
  unsigned int signature=0;
  BitIterator endIt=this->neighbEnd(it);
  int pos=this->neighbCubeInitPosition;  // defined in EuclBitSetT.h, depending on dimension
  for(NeighbIterator nbIt=this->neighbBegin(it);nbIt<endIt;++nbIt){
    signature |= nbIt.getBit() << pos++;
  }
  signature &= ~(1 << midBit);
  signature=((signature & ~mask) >> 1) | (signature & mask);
  return 1 & (acyclicConfigsD3[signature >> 3] >> (signature & 7)); // 1 in acyclicConfigsD3 means the configuration is acyclic
}

/************************************************************************************/
// A version which additionally counts the number of neighbors

template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclicLT(const BitIterator& it,int& count) const{
  unsigned int signature=0;
  BitIterator endIt=this->neighbEnd(it);
  unsigned int pos=this->neighbCubeInitPosition;  // defined in EuclBitSetT.h, depending on dimension
  count=0;
  for(NeighbIterator nbIt=this->neighbBegin(it);nbIt<endIt;++nbIt){
    bool bit=nbIt.getBit();
    if(bit && pos!=midBit) ++count;
    signature |= bit << pos++;
  }
  signature &= ~(1 << midBit);
  signature=((signature & ~mask) >> 1) | (signature & mask);
  return 1 & (acyclicConfigsD3[signature >> 3] >> (signature & 7)); // 1 in acyclicConfigsD3 means the configuration is acyclic
}

/************************************************************************************/
//

template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclicLT_BCI(const BitCoordIterator& it) const{
  return neighbAcyclicLT(it);
}

/************************************************************************************/
// Unfinished variant with separate treatment of boundary points

/*
template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclic(const BitCoordIterator& it) const{
  const uint midBit=int(0.5+pow(3.0,this->embDim()))/2;
  const uint mask= (1 << midBit)-1;
  unsigned int signature=0;
  if(1){
//fcout << "Testing for " << it  << std::endl;
    BitIterator endIt=this->bdNeighbEnd(it);
    int pos=0;
//fcout << "Testing for (2)" << it  << std::endl;
    for(BdNeighbIterator nbIt=this->bdNeighbBegin(it);nbIt<endIt;++nbIt){
      signature = signature | (nbIt.getBit() << pos++);
    }
  }else{
    BitIterator endIt=this->neighbEnd(it);
    int pos=0;
    for(NeighbIterator nbIt=this->neighbBegin(it);nbIt<endIt;++nbIt){
      signature = signature | (nbIt.getBit() << pos++);
    }
  }
  signature=signature & ~(1 << midBit);
  signature=((signature & ~mask) >> 1) | (signature & mask);

  return 1 & (acyclicConfigsD3[signature >> 3] >> (signature & 7)); // 1 in acyclicConfigsD3 means the configuration is acyclic
}
*/

/************************************************************************************/
// remove cubes whose intersection with the rest is acyclic

template <typename P_EuclSet>
CubSetT<P_EuclSet>& CubSetT<P_EuclSet>::shaveBI(){
  readAcyclicConfigs();  // check and read if necessary

  typename CubSetT<P_EuclSet>::PointIterator itEnd=this->end();
  for(PointIterator it=this->begin();it<itEnd;++it){
    if((this->*neighbAcyclicBI)(it)){
      it.clearBit();
    }
  }
  return *this;
}

// -------------------------------------------------------------------------------------- //

template <typename P_EuclSet>
CubSetT<P_EuclSet>& CubSetT<P_EuclSet>::shave(){
  if(embeddingDim > 3 || embeddingDim < 1) throw std::runtime_error("LT shave works only in dim 2 or 3!");
  neighbAcyclicBI=neighbAcyclicLT;
  shaveBI();
  return *this;
}



/************************************************************************************/
// remove cubes whose intersection with the rest is acyclic
// unles the cube is in the subset
// Added for persistence computation in 3d

template <typename P_EuclSet>
CubSetT<P_EuclSet>& CubSetT<P_EuclSet>::shaveWithFixedSubset(const CubSetT<P_EuclSet>& A_subset){
  readAcyclicConfigs();  // check and read if necessary

  // Before using make sure that neighbAcyclicBI  is properly initialized
  typename CubSetT<P_EuclSet>::BitIterator itEnd=this->end();
  typename CubSetT<P_EuclSet>::BitIterator it=this->begin();
  typename CubSetT<P_EuclSet>::BitIterator itSubset=A_subset.begin();
  for(;it<itEnd;++it,++itSubset){
    if(it.getBit() && (this->neighbAcyclicLT)(it) && !itSubset.getBit()){
      it.clearBit();
    }
  }
  return *this;
}

/************************************************************************************/
// Construct acyclic subspace using BitIterator(s)

template <typename P_EuclSet>
int CubSetT<P_EuclSet>::acyclicSubspaceBI(CubSetT& acSubsp) const{
  CubSetT<P_EuclSet> notProcessedCubes(*this); // We keep here cubes whose connected components were not identified yet
  int numberOfComponents=0;
  acSubsp.clear();

  PointIterator leadingIt(notProcessedCubes);  // it will point to the first cube in a new component
  BitIterator copyEnd=notProcessedCubes.end();
  // If the set is empty, we return
  if( !(leadingIt<copyEnd) ) return numberOfComponents;

  // Process the component of *leadingIt
  do{
    ++numberOfComponents;
    BitIterator it(acSubsp,leadingIt); // it will be the starting point of the acyclic subset in this component


    std::deque<BitIterator> acSubspCandidates;  // to store the candidates for the acyclic subset
    std::deque<BitIterator> others;  // to store cubes not added to the acyclic subsets
    acSubspCandidates.push_back(BitIterator(acSubsp,it));
    bool firstPoint=true;
    while(!acSubspCandidates.empty()){ // as long as we have candidates
      // we remove a candidate from the front of the queue
      BitIterator it=acSubspCandidates.front();
      acSubspCandidates.pop_front();
      if(it.getBit()) continue;  // If already in the acyclic subset, we may skip it
      if(firstPoint || (acSubsp.*neighbAcyclicBI)(it)){ // If can be added to the acyclic subset
        firstPoint=false;
        it.setBit();                                  // add it to the acyclic subset
        BitIterator(*this,it).clearBit();             // remove it from the set
        BitIterator(notProcessedCubes,it).clearBit(); // by removing mark that its connected component already identified
        // an we add the appropriate neighbors to the queue of candidates for the acyclic set
        BitIterator endIt=acSubsp.neighbEnd(it);
        for(NeighbIterator nbIt=acSubsp.neighbBegin(it);nbIt<endIt;++nbIt){
          if(                                    // if
            BitIterator(*this,nbIt).getBit() // &&  // belongs to the set
          ){
            acSubspCandidates.push_back(nbIt);
          }
        }
      }else{
        others.push_back(it); // since cannot be added to acyclic subset, keep it for later processing of connected component
      }
    }

    // Done with the acyclic subset, now process the cubes in the others queue - they may have neighbors indicating the connected component
    while(!others.empty()){
      // take the first one
      BitIterator it=others.front();
      others.pop_front();
      if(!BitIterator(notProcessedCubes,it).getBit()) continue;  // Do not process cubes whose component were identified already
      BitIterator(notProcessedCubes,it).clearBit();              // otherwise mark that component identified by removing from notProcessed
      BitIterator endIt=acSubsp.neighbEnd(it);
      for(NeighbIterator nbIt=acSubsp.neighbBegin(it);nbIt<endIt;++nbIt){ // go through neighborhood and
        if(                                    // if
          BitIterator(notProcessedCubes,nbIt).getBit()                    // add all not processsed cubes
        ){
          others.push_back(nbIt);
        }
      }
    }
    ++leadingIt;        // go to the next cube not processed cube (in a new component)
  }while(leadingIt<copyEnd);
  return numberOfComponents;
}

/************************************************************************************/
// The intersection of a set of neighbors of a pixel is defined as simple if in every
// direction the intersection of the projections on that direction is non-empty
// !!!!!!! Warning: this method returns an int and not a bool !!!!!!
template <typename P_EuclSet>
int CubSetT<P_EuclSet>::simpleIntersection(vector<Pixel> pixels) const{
  int k;
  // if no pixel from the vector is in the bitmap, there is no intersection,
  // so return false
  for(k=0;k<(int)pixels.size();++k) if(containsPixel(pixels[k]))goto found;
  return 0;   // 0 means not acyclic
  found:


//  Although embDim() can evaluate at compile time, the compiler is not aware of this fact
//  when compiling the derivative class of a class given as template parameter
//  and complains about variable size arrays
//  typename P_EuclSet::interval iv[this->embDim()];
  typename P_EuclSet::interval* iv=new typename P_EuclSet::interval[this->embDim()];
  for(int i=0;i<this->embDim();++i) iv[i]= typename P_EuclSet::interval(pixels[k].coord[i],pixels[k].coord[i]+1);
  for(int l=k+1;l<(int)pixels.size();++l){
    if(!containsPixel(pixels[l])) continue;
    for(int i=0;i<this->embDim();++i){
      iv[i]*= typename P_EuclSet::interval(pixels[l].coord[i],pixels[l].coord[i]+1);
      if(iv[i].empty()){
        delete[] iv;
        return -1; // acyclicity unknown
      }
    }
  }
  delete[] iv;
  return 1; // acyclicity true;
}



/************************************************************************************/
// The intersection of a set of neighbors of a pixel is defined as simple if in every
// direction the intersection of the projections on that direction is non-empty

// This is an oversimplified version of the original simple intersection - does not produce good results
template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclicOSSI(const BitCoordIterator& it) const{
  vector<Pixel> neighbors;
  Pixel p(it);
  getNeighbors(p,neighbors);
  // simple intersection means in particular an acyclic intersection
  // so the pixel may be added
  int acyclicity=simpleIntersection(neighbors);
  if(acyclicity  == -1) return 0;
  else return acyclicity;
}

/************************************************************************************/
// The intersection of a set of neighbors of a pixel is defined as simple if in every
// direction the intersection of the projections on that direction is non-empty


template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclicSI(const BitCoordIterator& it) const{
  vector<Pixel> neighbors;
  Pixel p(it);
  getNeighbors(p,neighbors);
  // simple intersection means in particular an acyclic intersection
  // so the pixel may be added
  int acyclicity=simpleIntersection(neighbors);
  if(acyclicity<0){
//    CubSetT<P_EuclSet> nbhd(5),acSubsNbhd(5);
    CubSetT<P_EuclSet> nbhd(3),acSubsNbhd(3); // tested and it seems that 3 may be used safely here
    this->getNeighborhood3(p,nbhd);           // and here
//    nbhd.acyclicSubspaceBCI(acSubsNbhd);// Produces smaller acyclic subspaces then the call to the original version below
    nbhd.acyclicSubspaceOrg(acSubsNbhd);  // Keep here the call to the original version as long as
                                          // it is understood why the above gives smaller acyclic subsets
    acyclicity=(nbhd==acSubsNbhd);
  }
  return acyclicity;
}

/************************************************************************************/
// Version with explicit conversion from BitIterator to BitCoordIterator
// needed for assignments to method pointers

template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclicSI_BI(const BitIterator& it) const{
  return neighbAcyclicSI(it);
}


/************************************************************************************/
// The intersection of a set of neighbors of a pixel is defined as simple if in every
// direction the intersection of the projections on that direction is non-empty
// Recursive version

template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclicSIR(const BitCoordIterator& it) const{
  vector<Pixel> neighbors;
  Pixel p(it);
  getNeighbors(p,neighbors);
  // simple intersection means in particular an acyclic intersection
  // so the pixel may be added
  int acyclicity=simpleIntersection(neighbors);
  if(acyclicity  == -1){  // -1 means acyclicity not determined
    CubSetT<P_EuclSet> nbhd(5),acSubsNbhd(5); // The size needs to be 5 but I do not remember why - should be tested for 3
    getNeighborhood5(p,nbhd);                 // should be tested if 3 may be used safely here
    acyclicity=(nbhd.acyclicSubspaceBCI(acSubsNbhd)==1 && nbhd.cardinality()==0 ? 1 : 0);
  }
  return acyclicity;
}

/************************************************************************************/
// The intersection of a set of neighbors of a pixel is defined as simple if in every
// direction the intersection of the projections on that direction is non-empty
// Recursive version

template <typename P_EuclSet>
bool CubSetT<P_EuclSet>::neighbAcyclicHOM(const BitCoordIterator& it) const{
  typedef CubSetT<P_EuclSet> BCubSet;
  typedef CubCellSetT<P_EuclSet,void*> BCubCelSet;
  typedef CRef<BCubSet> BCubSetCR;
  typedef CubSetFunctors<BCubSet,BCubCelSet> CubSetFunct;

  BCubSetCR nbhdCR(new BCubSet(5));   // should be tested if 3 may be used safely here
  Pixel p(it);
  getNeighborhood5(p,nbhdCR());       // should be tested if 3 may be used safely here

  fcout.turnOff();
  CRef<HomologySignature<int> > signCR=CubSetFunct::HomologyViaAlgebraicReductions(nbhdCR);
  fcout.turnOn();
  if(signCR().size()>1) return false;
  return signCR()[0].rank()==1;
}

/************************************************************************************/
// remove cubes whose intersection with the rest is acyclic

template <typename P_EuclSet>
CubSetT<P_EuclSet>& CubSetT<P_EuclSet>::shaveBCI(){

  PointCoordIterator endIt=this->end();
  for(PointCoordIterator it(*this);it<endIt;++it){
    if((this->*neighbAcyclicBCI)(it)){
      it.clearBit();
    }
  }
  return *this;
}

/************************************************************************************/

template <typename P_EuclSet>
int CubSetT<P_EuclSet>::acyclicSubspaceBCI(CubSetT& acSubsp) const{

  CubSetT<P_EuclSet> notProcessedCubes(*this); // We keep here cubes whose connected components were not identified yet
  int numberOfComponents=0;
  acSubsp.clear();

  PointCoordIterator leadingIt(notProcessedCubes);  // it will point to the first cube in a new component
  BitCoordIterator copyEnd=notProcessedCubes.end();
  // If the set is empty, we return
  if( !(leadingIt<copyEnd) ) return numberOfComponents;

  // Process the component of *leadingIt
  do{
    ++numberOfComponents;
    BitCoordIterator it(acSubsp,leadingIt); // it will be the starting point of the acyclic subset in this component


    std::deque<BitCoordIterator> acSubspCandidates;  // to store the candidates for the acyclic subset
    std::deque<BitCoordIterator> others;  // to store cubes not added to the acyclic subsets
    acSubspCandidates.push_back(BitCoordIterator(acSubsp,it));
    bool firstPoint=true;
    while(!acSubspCandidates.empty()){ // as long as we have candidates
      // we remove a candidate from the front of the queue
      BitCoordIterator it=acSubspCandidates.front();
      acSubspCandidates.pop_front();
      if(it.getBit()) continue;  // If already in the acyclic subset, we may skip it
      if(firstPoint || (acSubsp.*neighbAcyclicBCI)(it)){ // If can be added to the acyclic subset
        firstPoint=false;
        it.setBit();                                  // add it to the acyclic subset
        BitCoordIterator(*this,it).clearBit();             // remove it from the set
        BitCoordIterator(notProcessedCubes,it).clearBit(); // by removing, we mark that its connected component already identified
        // and we add the appropriate neighbors to the queue of candidates for the acyclic set
        BitCoordIterator endIt=acSubsp.neighbEnd(it);
        for(NeighbIterator nbIt=acSubsp.neighbBegin(it);nbIt<endIt;++nbIt){
          if(                                    // if
            BitCoordIterator(*this,nbIt).getBit() // &&  // belongs to the set
          ){
            acSubspCandidates.push_back(nbIt);
          }
        }
      }else{
        others.push_back(it); // since cannot be added to acyclic subset, keep it for later processing of connected component
      }
    }

    // Done with the acyclic subset, now process the cubes in the others queue - they may have neighbors indicating the connected component
    while(!others.empty()){
      // take the first one
      BitCoordIterator it=others.front();
      others.pop_front();
      if(!BitCoordIterator(notProcessedCubes,it).getBit()) continue;  // Do not process cubes whose component were identified already
      BitCoordIterator(notProcessedCubes,it).clearBit();              // otherwise mark that component identified by removing from notProcessed
      BitCoordIterator endIt=acSubsp.neighbEnd(it);
      for(NeighbIterator nbIt=acSubsp.neighbBegin(it);nbIt<endIt;++nbIt){ // go through neighborhood and
        if(                                    // if
          BitCoordIterator(notProcessedCubes,nbIt).getBit()                    // add all not processsed cubes
        ){
          others.push_back(nbIt);
        }
      }
    }
    ++leadingIt;        // go to the next not processed cube (in a new component)
  }while(leadingIt<copyEnd);
  return numberOfComponents;
}

/************************************************************************************/

// This is the original version of the acyclic subspace method
// Now renamed to acyclicSubspaceOrg
// It is still used in the neighbAcyclicSI method, becasue then it produces better
// (larger) acyclic subsets. However it is unclear why, the difference between
// this version and the earlier version in this respect must still be figured out
//
// It can also work as the replacement for the method above,
// but only for connected spaces (does not count components, treats only the first component)

template <typename P_EuclSet>
int CubSetT<P_EuclSet>::acyclicSubspaceOrg(CubSetT& acSubsp) const{
  acSubsp.clear();
  PointIterator it(*this);
  // If the set is empty, we return
  //if(!it.findPoint()) return;
  if(!it.findPoint()) return 1;
  // Otherwise we begin with the pixel found
  // as the last (and in this case also first) pixel added
  // to the constructed set
  Pixel q(it);
  acSubsp.addPixel(q);
  // this set and queue will store candidates to be analyzed
  // we need set and queue, because the set guarantees no repetitions
  // and the queue guarantees proper order of processing
  CubSetT candidates(acSubsp);
  std::deque<Pixel> pixelsToProcess;
  // The first candidates come from the neighborhood of the first pixel
  vector<Pixel> neighbors;
  getNeighbors(q,neighbors);
  // -- MM  cout << "*** Starting with " << q << " are " << std::endl;
  // We add only these pixels in the neighborhood which belong to the set
  for(int k=0;k<(int)neighbors.size();++k){
    if(containsPixel(neighbors[k])){
      pixelsToProcess.push_back(neighbors[k]);
      candidates.addPixel(neighbors[k]);
    }
  }

  // Now we start the main loop of processing
  while(!pixelsToProcess.empty()){
    // we remove a candidate from the front of the queue
    Pixel p=pixelsToProcess.front();
    pixelsToProcess.pop_front();
    candidates.removePixel(p);

    // To verify if the pixel may be added we first construct the neighbors
    vector<Pixel> neighbors;
    getNeighbors(p,neighbors);
    // simple intersection means in particular an acyclic intersection
    // so the pixel may be added
    int acyclicity=acSubsp.simpleIntersection(neighbors);
    if(acyclicity<0){
//      CubSetT<P_EuclSet> nbhd(5),acSubsNbhd(5); // The 5 neighborhood at some stage was needed to guarantee empty collar
                                                  // But this version seems to be slightly slower and most likely not needed anymore
      CubSetT<P_EuclSet> nbhd(3),acSubsNbhd(3); // Tested, and it seems that there is no need for 5 here
      acSubsp.getNeighborhood3(p,nbhd);
//      nbhd.acyclicSubspaceBCI(acSubsNbhd);  // works worse (smaller acyclic subset is produced)
      nbhd.acyclicSubspaceOrg(acSubsNbhd);
      acyclicity=(nbhd==acSubsNbhd);
    }

    if(acyclicity){
      // we add it to the constructed set
      acSubsp.addPixel(p);
      // an we add the appropriate neighbors to the queue of candidates
      for(int k=0;k<(int)neighbors.size();++k){
        if(
          containsPixel(neighbors[k]) &&
          !acSubsp.containsPixel(neighbors[k]) &&
          !candidates.containsPixel(neighbors[k])
        ){
          candidates.addPixel(neighbors[k]);
          pixelsToProcess.push_back(neighbors[k]);
        }
      }
    }
  }
  return 1;
}


#endif //_TOPCUBSETT_HPP_
/// @}

