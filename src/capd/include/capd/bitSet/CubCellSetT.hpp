/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CubCellSetT.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#if !defined(_CUBCELLSETT_H_)
#define _CUBCELLSETT_H_
#include "capd/bitSet/CubCellSetT.h"



/************************************************************************************/
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::CubCellSetT(const CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>& A_org, bool clear):
    P_EuclSet((const P_EuclSet&)(A_org),clear){
    }

/************************************************************************************/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::CubCellSetT(const P_EuclSet& A_EuclSet){
  std::vector<int> bitWidth(A_EuclSet.embDim());
  for(int i=0;i<this->embDim();++i){
    bitWidth[i]=2*A_EuclSet.getUnpaddedWidth(i)+1;
  }

  CubCellSetT<P_EuclSet,P_CubCellSetSimplificator> internalCubSet(&bitWidth[0],true);  // true means clear
  typename P_EuclSet::PointCoordIterator it(A_EuclSet.begin());
  typename P_EuclSet::PointCoordIterator itEnd(A_EuclSet.end());
  for(;it<itEnd;++it){
    std::vector<int> coord(A_EuclSet.embDim());
    for(int i=0;i<this->embDim();++i) coord[i]=2*it[i]+1;
    BitIterator internIt(internalCubSet,&coord[0]);
    NeighbIterator nbIt=internalCubSet.neighbBegin(internIt);
    BitIterator nbhdEndIt=internalCubSet.neighbEnd(internIt);
    for(;nbIt<nbhdEndIt;++nbIt){
      nbIt.setBit();
    }
  }
  swap(internalCubSet,*this);
}

/************************************************************************************/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::CubCellSetT(const RepSet<ElementaryCube>& A_RepSetOfElementaryCube){
  std::vector<int> minCoord(this->embDim());
  std::vector<int> maxCoord(this->embDim());
  std::vector<int> bitWidth(this->embDim());
  A_RepSetOfElementaryCube.enclosingBox(&minCoord[0],&maxCoord[0]);
  for(int i=0;i<this->embDim();++i){
    bitWidth[i]=2*(maxCoord[i]-minCoord[i])+1;
    // -- MM  std::cout << "--- interval[" << i << "] is [" << minCoord[i] << "," << maxCoord[i] << "] of width " << bitWidth[i] << std::endl; // *** DEBUG *** //
  }
  CubCellSetT<P_EuclSet,P_CubCellSetSimplificator> internalCubSet(&bitWidth[0],true); // true means clear

  typename std::set<ElementaryCube>::const_iterator pos;
  for(pos=A_RepSetOfElementaryCube.begin(); pos != A_RepSetOfElementaryCube.end(); ++pos){
    const ElementaryCube& current=*pos;
    if(current.embeddingDimension()!=this->embDim()) throw std::runtime_error("CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::importRepSetOfElementaryCube: incorrect embedding dimension");
    std::vector<int> coords(this->embDim());
    std::vector<int> minCoords(this->embDim());
    std::vector<int> maxCoords(this->embDim());
    for(int i=0;i<this->embDim();++i){
      minCoords[i]=coords[i]=2*(current.leftCoordinate(i)-minCoord[i]);
      maxCoords[i]=minCoords[i]+2*(int)current.nonDegenerate(i);
    }
    loop:
    while(true){
      typename P_EuclSet::Pixel p(&coords[0]);
      internalCubSet.addPixel(p);
      for(int i=0;i<this->embDim();++i){
        ++coords[i];
        if(coords[i]<=maxCoords[i]) goto loop;
        else coords[i]=minCoords[i];
      }
      break;
    }
  }
  swap(internalCubSet,*this);
}

/************************************************************************************/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::CubCellSetT(const RepSet<ElementaryCell>& A_RepSetOfElementaryCell){
  std::vector<int> minCoord(this->embDim());
  std::vector<int> maxCoord(this->embDim());
  std::vector<int> bitWidth(this->embDim());
  A_RepSetOfElementaryCell.enclosingBox(&minCoord[0],&maxCoord[0]);
  for(int i=0;i<this->embDim();++i){
    bitWidth[i]=2*(maxCoord[i]-minCoord[i])+1;
  }
  CubCellSetT<P_EuclSet,P_CubCellSetSimplificator> internalCubSet(&bitWidth[0],true); // true means clear

  typename std::set<ElementaryCell>::const_iterator pos;
  for(pos=A_RepSetOfElementaryCell.begin(); pos != A_RepSetOfElementaryCell.end(); ++pos){
    const ElementaryCell& current=*pos;
    if(current.embeddingDimension()!=this->embDim()) throw std::runtime_error("CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::importRepSetOfElementaryCube: incorrect embedding dimension");
    std::vector<int> coords(this->embDim());
    for(int i=0;i<this->embDim();++i){
      coords[i]=2*(current.leftCoordinate(i)-minCoord[i])+(int)current.nonDegenerate(i);
    }
    typename P_EuclSet::Pixel p(&coords[0]);
    internalCubSet.addPixel(p);
  }
  swap(internalCubSet,*this);
}


/************************************************************************************/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
void CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::addEmptyCollar(){
  int c[theDim];
  for(int i=0;i<theDim;++i){
    c[i]=4+this->getUnpaddedWidth(i);
  }
  CubCellSetT<P_EuclSet> newCubCelSet(c,true); // true means clear
  for(PointCoordIterator it=this->begin(); it<this->end();++it){
    for(int i=0;i<theDim;++i)  c[i]=2+it[i];
    BitIterator it2(newCubCelSet,c);
    it2.setBit(1);
  }
  swap(*this,newCubCelSet);
}

/************************************************************************************/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
void CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::rescale(int A_factor){
  if(A_factor<1) throw std::runtime_error("CubCellSetT::rescale: factor must be greater than zero");
  int dim=this->embDim();
  std::vector<int> bitWidth(dim);
  for(int i=0;i<this->embDim();++i){
    bitWidth[i]=A_factor*(this->getUnpaddedWidth(i)/2)*2+1;
  }
  P_EuclSet internalCubSet(&bitWidth[0],true);
  typename P_EuclSet::PointCoordIterator it(*this);
  for(it=this->begin();it<this->end();++it){
    std::vector<int> coords(dim),minCoords(dim),maxCoords(dim);
    for(int i=0;i<this->embDim();++i){
      minCoords[i]=coords[i]=(it[i]/2)*A_factor*2+it[i]%2;
      maxCoords[i]=(it[i]/2+it[i]%2)*A_factor*2-it[i]%2;
    }
    loop:
    while(true){
      typename P_EuclSet::Pixel p(&coords[0]);
      internalCubSet.addPixel(p);
      for(int i=0;i<this->embDim();++i){
        ++coords[i];
        if(coords[i]<=maxCoords[i]) goto loop;
        else coords[i]=minCoords[i];
      }
      break;
    }
  }
  swap(internalCubSet,*this);
}

/************************************************************************************/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
void CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::rescale(const int A_factor[]){
  for(int i=0;i<this->embDim();++i) if(A_factor[i]<1) throw std::runtime_error("CubCellSetT::rescale: factor must be greater than zero");
  int dim=this->embDim();
  std::vector<int> bitWidth(dim);
  for(int i=0;i<this->embDim();++i){
    bitWidth[i]=A_factor[i]*(this->getUnpaddedWidth(i)/2)*2+1;
  }
  P_EuclSet internalEuclSet(&bitWidth[0],true);
  typename P_EuclSet::PointCoordIterator it(*this);
  for(it=this->begin();it<this->end();++it){
    std::vector<int> coords(dim),minCoords(dim),maxCoords(dim);
    for(int i=0;i<this->embDim();++i){
      minCoords[i]=coords[i]=(it[i]/2)*A_factor[i]*2+it[i]%2;
      maxCoords[i]=(it[i]/2+it[i]%2)*A_factor[i]*2-it[i]%2;
    }
    loop:
    while(true){
      typename P_EuclSet::Pixel p(&coords[0]);
      internalEuclSet.addPixel(p);
      for(int i=0;i<this->embDim();++i){
        ++coords[i];
        if(coords[i]<=maxCoords[i]) goto loop;
        else coords[i]=minCoords[i];
      }
      break;
    }
  }
  swap(internalEuclSet,*this);
}

// ********** coReduce methods ********** //

/************************************************************************************/

// Verify if the given pixel represents a vertex in the
// representalbe set, i.e. if it is degenerate in all dimensions
// Iterator version
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::isVertex(BitCoordIterator& A_it) const{
  for(int i=0;i<this->embDim();++i){   // consider all directions
    if(A_it.odd(i)){ // if the cell represented by pixel is nondegenerate in this direction
      return false;
    }
  }
  return true;
}

/************************************************************************************/

// Construct all codimension one cofaces
// Iterator version
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
void CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::getCoFaces(
  BitCoordIterator& A_it,
  std::vector<BitCoordIterator>& A_codimOneCofacesIterators
)const{
  for(int i=0;i<this->embDim();++i){  // consider all directions
    if(!A_it.odd(i)){ // if the cell represented by pixel is degenerate in this direction
                                 // it has two cofaces extending in this direction
      A_it.decInDir(i);;         // get the first one and check if it belongs to the set
                                 // disregard the case outside the bitmap (A_it[i]<0)
      if( A_it[i]>=0 && A_it.getBit() ){
        A_codimOneCofacesIterators.push_back(A_it);  // add the coface iterator to the vector
      }
      A_it.incInDir(i);            // restore the iterator

      A_it.incInDir(i);            // similarly check the other side
      if( A_it[i]<=this->paddedBitWidth[i]-1 && A_it.getBit() ){
        A_codimOneCofacesIterators.push_back(A_it);  // add the coface iterator to the vector
      }
      A_it.decInDir(i);            // restore the iterator
    }
  }
}

/************************************************************************************/

// Verify if the given pixel represents a cofree cell in the representable set,
// i.e. a cell which has exaclty one face of dimension one lower in the representable set
// (codimension one face)
// If true, return the codimension one face
// Iterator version
/* Seems to be slightly slower than the version below, but may turn out
   to be faster with the planned new iterators
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::isFreeCoFace(BitCoordIterator& A_coFaceIt, BitCoordIterator& A_faceIt) const{
  bool faceFound=false;
  for(int i=0;i<this->embDim();++i){  // consider all directions
    // Note: since we move the iterator only in the directions, where the coordinate is odd,
    // there is no risk of moving out of bitmap, so no checks are needed
    if(A_coFaceIt[i]%2 != 0){            // if the cell represented by pixel is nondegenerate in this direction
                                   // it has two faces extending in this direction
      BitCoordIterator coFaceItCopy=A_coFaceIt;
      coFaceItCopy.decInDir(i);            // get the first one and check if it belongs to the set
                                   // disregard the case outside the bitmap (coord[i]<0)
      if(coFaceItCopy.getBit()){
        if(faceFound){     // face is not unique, so not a free coface
          return false;
        }
        faceFound=true;    // this may be a free face, if no more will be found
        A_faceIt=coFaceItCopy;     // keep face just in case it is unique
      }
      coFaceItCopy=A_coFaceIt;            // restore the iterator

      coFaceItCopy.incInDir(i);            // similarly check the other side
      if(coFaceItCopy.getBit()){
        if(faceFound){
          return false;
        }
        faceFound=true;
        A_faceIt=coFaceItCopy;     // keep face just in case it is unique
      }
    }
  }
  return faceFound; //
}
*/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::isFreeCoFace(BitCoordIterator& A_coFaceIt, BitCoordIterator& A_faceIt) const{
  bool faceFound=false;
  for(int i=0;i<this->embDim();++i){  // consider all directions
    // Note: since we move the iterator only in the directions, where the coordinate is odd,
    // there is no risk of moving out of bitmap, so no checks are needed
    if(A_coFaceIt.odd(i)){            // if the cell represented by pixel is nondegenerate in this direction
                                   // it has two faces extending in this direction
      A_coFaceIt.decInDir(i);            // get the first one and check if it belongs to the set
                                   // disregard the case outside the bitmap (coord[i]<0)
      if(A_coFaceIt.getBit()){
        if(faceFound){     // face is not unique, so not a free coface
          A_coFaceIt.incInDir(i);        // restore the iterator
          return false;
        }
        faceFound=true;    // this may be a free face, if no more will be found
        A_faceIt=A_coFaceIt;     // keep face just in case it is unique
      }
      A_coFaceIt.incInDir(i);            // restore the iterator

      A_coFaceIt.incInDir(i);            // similarly check the other side
      if(A_coFaceIt.getBit()){
        if(faceFound){
          A_coFaceIt.decInDir(i);        // restore the iterator
          return false;
        }
        faceFound=true;
        A_faceIt=A_coFaceIt;     // keep face just in case it is unique
      }
      A_coFaceIt.decInDir(i);            // restore the iterator
    }
  }
  return faceFound; //
}

/************************************************************************************/

// Search the set for the standard cofree pair or a pseudopair (vertex,emptySet)
// A pseudo pair is a vertex of a closed component (free vertex).
// The search is started from the starting iterator provided.
// Return true if a cofree pair or pseudo cofree pair found
// the method is assumed to work on a copy of the original bitmap.
// On every call one connected component is searched and the pixels searched
// are removed from the copy. The original is kept intact
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::findCoFreeFaceOrFreeVertex(
  const CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>& source,  // the original bitmap
  PointIterator& A_startIter,         // the iterator in the copy from which to start
  BitCoordIterator& A_it              // the pixel of the cofree pair if found
)const{
  while(true){
    std::deque<BitCoordIterator> pixelIteratorsToProcess; // a queue to keep the pixels in the copy
                                                          // the neighbors of these pixels are checked if the belong to the component
/*  old version, but probably the new below is better - not tested!!!!
    for(;A_startIter.findPoint();A_startIter.advance()){        // serach if there is still a pixel in the copy
      pixelIteratorsToProcess.push_back(BitCoordIterator(A_startIter));
      A_startIter.advance();
      goto constructComponent;                          // pixel found, so find its component
    }
*/
    // new - simplified version - to be tested!!!
    if(!(A_startIter<this->end())) return false;          // nothing found, so exit, indicating that nothing was found
    pixelIteratorsToProcess.push_back(BitCoordIterator(A_startIter));
    ++A_startIter;

    //    constructComponent:

    bool coFreeFaceFound=false;
    bool componentClosed=true;
    BitCoordIterator lastVertex(source);
    while(!pixelIteratorsToProcess.empty()){              // process as long as no new pixels are found in the component
      // remove a pixel from the front of the queue
      BitCoordIterator pIt=pixelIteratorsToProcess.front();
      pixelIteratorsToProcess.pop_front();

      // -- MM  fcout << "Processing " << pIt << std::endl;
      // -- MM  fcout << "   Queue size is " << pixelIteratorsToProcess.size() << std::endl;

      pIt.clearBit();                                     // mark as processed
      BitCoordIterator sourceIt(source,pIt);              // make a mirror iterator for the source

      int nonDegenerateCounter=0;
      int codimOneFaceCounter=0;
      for(int i=0;i<this->embDim();++i){                             // consider all directions
        // -- MM  fcout << "  =this->embDim()=" << i << std::endl;
        const int& iCoord=pIt[i];
        bool nonDegenerate=pIt.odd(i);                      // is the cell represented by pixel nondegenerate in this direction ?
                                                          // (Keep it here, do not optimize!)
        if(nonDegenerate) ++nonDegenerateCounter;
        // -- MM  fcout << "    nonDegenerate " << nonDegenerate << std::endl;
                                                          // it has two faces extending in this direction
        if(iCoord>0){                                     // make sure we are in the limits
          pIt.decInDir(i);                                // get the first one
          // -- MM  fcout << "    Trying- " << pIt << " with " << pIt.getBit() << std::endl;
          if(pIt.getBit()){
            pixelIteratorsToProcess.push_back(pIt);       // if it still is in the copy, add it to the queue for processing
            pIt.clearBit();
            // -- MM  fcout << "    Inserting " << pIt << std::endl;
          }
          if(nonDegenerate){                              // if this direction is nondegenerate, then we have a candidate for a free coFace
            if(BitCoordIterator(source,pIt).getBit()){    // if the pixel is in the source
              ++codimOneFaceCounter;                      // mark it as a coface
            }else{
              componentClosed=false;                      // if it is not in the source, the component is not closed
            }
            // -- MM  fcout << "    codimOneFaceCounter " << codimOneFaceCounter << std::endl;
          }
          pIt.incInDir(i);                                // restore the iterator
        }

        if(iCoord<this->paddedBitWidth[i]-1){
          pIt.incInDir(i);                                // similarly check the other side
          // -- MM  fcout << "    Trying+ " << pIt << " with " << pIt.getBit() << std::endl;
          if(pIt.getBit()){
            pixelIteratorsToProcess.push_back(pIt);
            pIt.clearBit();
            // -- MM  fcout << "    Inserting " << pIt << std::endl;
          }
          if(nonDegenerate){
            // -- MM  fcout << "    Bit " << BitCoordIterator(source,pIt) << " is " << BitCoordIterator(source,pIt).getBit() << std::endl;
            if(BitCoordIterator(source,pIt).getBit()){
              ++codimOneFaceCounter;
            }else{
              componentClosed=false;
            }
            // -- MM  fcout << "    codimOneFaceCounter " << codimOneFaceCounter << std::endl;
          }
          pIt.decInDir(i);                                 // restore the iterator
        }
      }                                                    // all faces considered
      if(nonDegenerateCounter==0) lastVertex=sourceIt;
      if(!coFreeFaceFound && codimOneFaceCounter==1 ){
        coFreeFaceFound=true;
        A_it=sourceIt;
        // -- MM  fcout << "    Found as cofree face: " << A_it << std::endl;
      }
    }
    if(!coFreeFaceFound && componentClosed){
      A_it=lastVertex;
      coFreeFaceFound=true;
      // -- MM  fcout << "    Found as cofree vertex: " << A_it << std::endl;
    }
    if(coFreeFaceFound) return true;
  }
}


/************************************************************************************/

// The method removes cotrivial pairs (cofree face and its unique face)
// from the representable set in a systematic fashion.
// Candidates for removal are taken from the neighborhood of the last removed
// pair and placed in a queue
// The homology does not change
// The method returns true (actually the number of loops with removals)
// if at least one pair was removed


template <typename P_EuclSet,typename P_CubCellSetSimplificator>
int CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::coReduce(){
  int loopCnt=0;

  CubCellSetT<P_EuclSet,P_CubCellSetSimplificator> marker(*this);
  PointIterator markerIter(marker);
  markerIter=marker.begin();

  while(true){
    BitCoordIterator iter(*this);
    if(!marker.findCoFreeFaceOrFreeVertex(*this,markerIter,iter)) return loopCnt;

    // -- MM   std::cout << "Reducing from " <<  iter << std::endl;
    BitCoordIterator iterCopy(iter); // keep a copy - if a vertex, it will be added back at the end
                                     //(0th homology generator)

    ++loopCnt;

    // -- MM    fcout << "BitmapT has length " << this->getBmpSizeInBytes() << " bytes " << std::endl;
    // -- MM    double tt2=Clock();
    CubCellSetT candidates(*this,true); // copy and clear
    // -- MM    fcout << "Candidates construction time is " << Clock()-tt2  << std::endl;
    std::deque<BitCoordIterator> pixelIteratorsToProcess;

    // This is a tricky start:
    // If we got a pseudo coFree face (a vertex), then
    // it is not a coFree face (has no faces at all)
    // So in the loop we generate its cofaces as the first true candidates for a coFree face
    pixelIteratorsToProcess.push_back(iter);
    iter.clearBit();

    // Now we start the main loop of processing
    while(!pixelIteratorsToProcess.empty()){
      // we remove a candidate from the front of the queue
      BitCoordIterator pIt=pixelIteratorsToProcess.front();
      pixelIteratorsToProcess.pop_front();
      BitIterator(candidates,pIt).clearBit();

      // Container for the cofaces
      vector<BitCoordIterator> coFaceIterators;
      // Container for the face, if the pixel is coFree
      BitCoordIterator faceOfIter(*this);
      if(isFreeCoFace(pIt,faceOfIter)){
        // remove coface given by pIt and its face given by faceOfIter
        pIt.clearBit();
        faceOfIter.clearBit();
        BitIterator(candidates,faceOfIter).clearBit();
        // the cofaces of the faceOfIter are further candidates
        getCoFaces(faceOfIter,coFaceIterators);
      }else{ // if not a coFree faceOfIter, its cofaces constitute candidates
             // in particular we move immediately here with the vertex acting as free coface
        getCoFaces(pIt,coFaceIterators);
      }
      // add the appropriate cofaces to the queue of candidates
      for(int k=0;k<(int)coFaceIterators.size();++k){
        if(
          coFaceIterators[k].getBit() &&
            !BitIterator(candidates,coFaceIterators[k]).getBit()
        ){
          BitIterator(candidates,coFaceIterators[k]).setBit();
          pixelIteratorsToProcess.push_back(coFaceIterators[k]);
        }
      }
    }
    if(isVertex(iterCopy)) iterCopy.setBit();  // restore the 0th generator
  }
  return loopCnt;
}


// ********** coReduce() methods for compact sets ********** //

// This is a version for compact sets. It should work faster than the version
// for general representable sets, because there is no need to check if
// the vertex is taken from a compact component

/************************************************************************************/

// Search the set for the standard cofree pair
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::findFreeCoFace(
  PointIterator& A_startIter,         // the iterator from which to start
  BitCoordIterator& A_it              // the coface iterator if found
)const{
  BitCoordIterator faceIt(*this);
  for(A_it=A_startIter;A_it<this->end();++A_it){
    if(isFreeCoface(A_it,faceIt)) return true;
  }
  return false;
}


/************************************************************************************/

// Search the set for a vertex
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::findVertex(
  PointIterator& A_startIter,         // the iterator from which to start
  BitCoordIterator& A_it              // the vertex iterator if found
)const{
  for(A_it=A_startIter;A_it<this->end();++A_it){
    if(isVertex(A_it)) return true;
  }
  return false;
}



/************************************************************************************/

// The method removes cotrivial pairs (cofree face and its unique face)
// from the representable set in a systematic fashion as in the coReduce above.
// However, under the assumption that the set is compact, there is no need
// to check if the initial vertex starting the process is taken from
// a compact component, so time may be saved by restarting the process from a
// vertex whenever no more free faces are available.

//  Note: Actually, this should also work for arbitrary representable sets
//  if the search for a vertex is preceded by a search for a free coface
//  The absence of such a coface would mean that the set is compact, so the
//  search for a vertex would be justified. So its a potential to speed up the
//  general method coReduce above.

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
int CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::coReduceCompactSet(){
  int loopCnt=0;

  PointIterator vertexSearchIter(*this);
  while(true){
    BitCoordIterator vertexIter(*this);
    for(;vertexSearchIter < this->end() ;++vertexSearchIter){
      vertexIter=BitCoordIterator(vertexSearchIter);
      // -- MM  fcout << "Trying " << *vertexIter << std::endl;
      if(vertexIter.getBit() and isVertex(vertexIter)) goto vertexFound;
    }
    return loopCnt;

    vertexFound:

    // -- MM  fcout << "Found " << *vertexIter << std::endl;
    // mark as the vertex indentifying the connected component
    BitCoordIterator componentVertex=vertexIter;
                                           // it will be added back at the end
                                           //(0th homology generator)
    ++loopCnt;

    std::deque<BitCoordIterator> pixelIteratorsToProcess;
    // A bitmap to mark elements on stack to avoid duplicates
    CubCellSetT queueMarker(*this,true);

    // We remove the vertex, as a free coface
    removeReductionPair(vertexIter,vertexIter); // coface == face means a pseudo reduction pair
                                                // consisting of a connected component vertex and empty set
    // and for the loop we generate cofaces of the vertex
    // as the first candidates for a free coface
    pixelIteratorsToProcess.push_back(vertexIter);
    BitCoordIterator vertexIterMarker(queueMarker,vertexIter);
    vertexIterMarker.setBit();
    bool vertexAsCoface=true;

    // Now we start the main loop of processing
    while(!pixelIteratorsToProcess.empty()){
      // we remove a candidate from the front of the queue
      BitCoordIterator cofaceIter=pixelIteratorsToProcess.front();
      pixelIteratorsToProcess.pop_front();
//      BitCoordIterator cofaceIterMarker(queueMarker,cofaceIter);
//      cofaceIterMarker.clearBit();
      if(!vertexAsCoface && !cofaceIter.getBit()){
        continue;
      }else{
        vertexAsCoface=false;
      }

      // Container for the cofaces
      vector<BitCoordIterator> coFaceIterators;
      // Container for the face, in case the coface is free
      BitCoordIterator faceIter(*this);
      if(isFreeCoFace(cofaceIter,faceIter)){
        // remove coface given by cofaceIter and its face given by faceIter
        removeReductionPair(cofaceIter,faceIter); // coface is free, face is companion
        // -- MM  fcout << "Reduced " << faceIter << " with " << cofaceIter << std::endl;
        // the cofaces of the faceIter are further candidates
        getCoFaces(faceIter,coFaceIterators);
      }else{ // if not a coFree faceIter, its cofaces constitute candidates
             // in particular we move immediately here with the vertex acting as free coface
        getCoFaces(cofaceIter,coFaceIterators);
      }
      // add the appropriate cofaces to the queue of candidates
      for(int k=0;k<(int)coFaceIterators.size();++k){
        if(
          coFaceIterators[k].getBit()
        ){
           BitCoordIterator coFaceIterMarker(queueMarker,coFaceIterators[k]);
           if(!coFaceIterMarker.getBit()){
             coFaceIterMarker.setBit();
             pixelIteratorsToProcess.push_back(coFaceIterators[k]);
           }
        }
      }
    }
    ++vertexSearchIter; // move to next point;
    componentVertex.setBit();  // restore the 0th generator
  }
  return loopCnt;
}

/************************************************************************************/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
int CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::coShave(){
  int count=0;
  for(int q=1;q<=this->embDim();++q){
    BitCoordIterator faceIt(*this);
    PointCoordIterator searchIt(*this);
    for(searchIt=this->begin();searchIt<this->end();++searchIt){
      if(searchIt.ownDim()==q && isFreeCoFace(searchIt,faceIt)){
        removeReductionPair(searchIt,faceIt); // searchIt is free, faceIt is companion
        ++count;
      }
    }
  }
  return count;
}


// ********** reduce() methods ********** //
// Fast - iterator based version - to be rewritten with iterators instead of pixels

/************************************************************************************/

// Verify if the given pixel represents a maximal cell in the
// representalbe set, i.e. if it is not a face of a cell of dimesion one greater
// Not needed  anymore
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::isMaximal(BitCoordIterator& A_it) const{
  for(int i=0;i<this->embDim();++i){   // consider all directions
    if(!A_it.odd()){ // if the cell is degenerate in this direction
      A_it.decInDir(i);
      if(A_it.getBit()){
        A_it.incInDir(i);
        return false;
      }
      A_it.incInDir(i);
      if(A_it.getBit()){
        A_it.decInDir(i);
        return false;
      }
    }
  }
  return true;
}

/************************************************************************************/

// Construct all codimension one faces
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
void CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::getFaces(
  BitCoordIterator& A_it,
  std::vector<BitCoordIterator>& A_facesIterators
) const{
  for(int i=0;i<this->embDim();++i){  // consider all directions
    if(A_it.odd(i)){ // if the cell is nondegenerate in this direction
      A_it.decInDir(i);
      if(A_it.getBit()){
        A_facesIterators.push_back(A_it);
      }
      A_it.incInDir(i);

      A_it.incInDir(i);
      if(A_it.getBit()){
        A_facesIterators.push_back(A_it);
      }
      A_it.decInDir(i);
    }
  }
}

/************************************************************************************/

// Verify if the given pixel represents a free cell in the representable set,
// i.e. a cell which is a face of exactly one cell of dimension one greater
// (codimension one coface)
// If true, return the codimension one coface
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::isFreeFace(BitCoordIterator& A_faceIt, BitCoordIterator& A_coFaceIt) const{
  bool codimOneCofaceFound=false;
  for(int i=0;i<this->embDim();++i){  // consider all directions
    // -- MM  fcout << "  direction is " << i  << std::endl;
    if(!A_faceIt.odd(i)){ // if the cell is degenerate in this direction
      if(A_faceIt[i]>0){
        A_faceIt.decInDir(i);
        // -- MM  fcout << " Trying down " << A_faceIt  << std::endl;
        if(A_faceIt.getBit()){
          // -- MM  fcout << " Testing down " << A_faceIt  << std::endl;
          if(codimOneCofaceFound){
            A_faceIt.incInDir(i);
            return false; // coface is not unique, so not a free face
          }
          // -- MM  fcout << " Found down " << A_faceIt  << std::endl;
          codimOneCofaceFound=true;  // this may be a free face, if no more will be found
          A_coFaceIt=A_faceIt;  // keep coface just in case it is unique
        }
        A_faceIt.incInDir(i);
      }

      if(A_faceIt[i]< A_faceIt.baseEuclBitSet()->getPaddedWidth(i)-1){
        A_faceIt.incInDir(i);
        // -- MM  fcout << " Trying up " << A_faceIt  << std::endl;
        if(A_faceIt.getBit()){
          // -- MM  fcout << " Testing up " << A_faceIt  << std::endl;
          if(codimOneCofaceFound){
            A_faceIt.decInDir(i);
            return false; // coface is not unique, so not a free face
          }
          // -- MM  fcout << " Found up " << A_faceIt  << std::endl;
          codimOneCofaceFound=true;  // this may be a free face, if no more will be found
          A_coFaceIt=A_faceIt;  // keep coface just in case it is unique
        }
        A_faceIt.decInDir(i);
      }
    }
  }
  return codimOneCofaceFound; // coface not found or found but not maximal - not a free face
}

/************************************************************************************/

// Add boundaries of every top dimensional cell to the set
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
void CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::fillWithSubEmbDimCells(){
  PointCoordIterator it(*this);
  for(;it<this->end();++it){
    if(it.ownDim()==this->embDim()){
      NeighbIterator nbIt=neighbBegin(it);
      BitIterator nbhdEndIt=neighbEnd(it);
      for(;nbIt<nbhdEndIt;++nbIt){
        nbIt.setBit();
      }
    }
  }
}

/************************************************************************************/

// Add boundaries of every  cell to the set
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
void CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::fillWithBoundaries(){
  PointCoordIterator it(*this);

  for(;it<this->end();++it){
    for(int i=0;i<this->embDim();++i){
      if(it.odd(i)){
        it.decInDir(i);
        it.setBit();
        it.incInDir(i);
        it.incInDir(i);
        it.setBit();
        it.decInDir(i);
      }
    }
  }
}

/************************************************************************************/

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
int CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::shave(){
  int count=0;
  for(int d=this->embDim()-1;d>=0;--d){
    BitCoordIterator coFaceIt(*this);
    PointCoordIterator searchIt(*this);
//    PointParIterator searchIt(*this);
    for(searchIt=this->begin();searchIt<this->end();++searchIt){
//      BitCoordIterator searchIt2(searchIt);
      if(searchIt.ownDim()==d && isFreeFace(searchIt,coFaceIt)){
        ++count;
        removeReductionPair(searchIt,coFaceIt); // searchIt is free, coFaceIt is companion
      }
    }
  }
  return count;
}

/************************************************************************************/

// The method removes trivial pairs (free face and its unique coface)
// from the representable set in a systematic fashion.
// Candidates for removal are taken from the neighborhood of the last removed
// pair and placed in a queue
// The homology does not change
// The method returns true if at least one pair was removed

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
int CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::reduce(int limit){
//int CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::reduce(){
  int loopCnt=0;

  typename P_EuclSet::PointIterator searchIt(*this);
  while(true){
    if(limit>0 && loopCnt>=limit) return loopCnt;

    BitCoordIterator faceIt(*this);
    // -- MMfcout << "At " << Pixel(searchIt)  << std::endl;
    BitCoordIterator coFaceIt(*this);
    for(searchIt=this->begin();searchIt<this->end();++searchIt){
      // -- MMfcout << " Testing for free coface " << Pixel(searchIt)  << std::endl;
      if(isFreeFace(faceIt=BitCoordIterator(searchIt),coFaceIt)){
        goto reductions;
      }
        // -- MMfcout << " Testing for free coface on exit: " << Pixel(searchIt)  << std::endl;
    }
    return loopCnt;

    reductions:
    ++loopCnt;
    // -- MMfcout << "Loop " << loopCnt << " with " << this->cardinality() << " cells" << std::endl;
    std::deque<BitCoordIterator> pixelIteratorsToProcess;

    pixelIteratorsToProcess.push_back(faceIt);
    // Now we start the main loop of processing
    while(!pixelIteratorsToProcess.empty()){
      // -- MMstd::cout << "   Internal loop with " << pixelIteratorsToProcess.size() << " pixels to process\n";
      // we remove a candidate from the front of the queue
      BitCoordIterator it=pixelIteratorsToProcess.front();
      pixelIteratorsToProcess.pop_front();
      if(!it.getBit()) continue;
      // -- MMfcout << " Trying " << Pixel(it)  << std::endl;

      // Container for the faces
      vector<BitCoordIterator> faceIterators;
      // Container for the coFace, if the pixel is coFree
      BitCoordIterator coFaceIt(*this);
      if(isFreeFace(it,coFaceIt)){
        // -- MMfcout << " Reducing " << Pixel(it) << " with " << Pixel(coFaceIt) << std::endl;
        // remove pixel and its coFace
        it.clearBit();
        coFaceIt.clearBit();
        // the cofaces of the coFace are futer candidates
        getFaces(coFaceIt,faceIterators);
      }else{ // if not a coFree coFace, its cofaces constitute candidates
        getFaces(it,faceIterators);
      }
      // add the appropriate cofaces to the queue of candidates
      for(int k=0;k<(int)faceIterators.size();++k){
        if(
          faceIterators[k].getBit()
        ){
          pixelIteratorsToProcess.push_back(faceIterators[k]);
        }
      }
    }
  }
  return loopCnt;
}

/************************************************************************************/

template <typename P_EuclSet,typename P_Reductor>
template<class ChainContainer>
void CubCellSetT<P_EuclSet,P_Reductor>::fillWith(const ChainT<ChainContainer>& chain){
  typename ChainT<ChainContainer>::const_iterator it;
  typedef typename ChainT<ChainContainer>::mapped_type ScalarType;
  for(it=chain.begin();it!=chain.end();++it){
    if(it->second != ScalarType(0)){
      int coords[theDim];
      it->first.getVals(reinterpret_cast<unsigned int*>(coords));
      BitCoordIterator it(*this,coords);
      it.setBit();
    }
  }
}


/*
template <typename P_EuclSet,typename P_Reductor>
template<typename P_Chain>
void CubCellSetT<P_EuclSet,P_Reductor>::reduce(P_Chain& A_chain){
  typename std::vector<ReductorType>::const_iterator it,itEnd;
  it=this->getReductors().begin();
  itEnd=this->getReductors().end();
  for(;it!=itEnd;++it){
    it->reduce(A_chain,*this);
  }
}

*/
// /*aaa*/ Hopefully this is now obsolete
/*
template <typename P_EuclSet,typename P_Reductor>
template<typename P_Chain>
void CubCellSetT<P_EuclSet,P_Reductor>::reduceInDimZero(P_Chain& A_chain){
  typename std::vector<ReductorType>::const_iterator it,itEnd;
  it=this->getReductors().begin();
  itEnd=this->getReductors().end();
  for(;it!=itEnd;++it){
    it->reduceInDimZero(A_chain,*this);
  }
}
*/

/*
template <typename P_EuclSet,typename P_Reductor>
template<typename P_Chain>
void CubCellSetT<P_EuclSet,P_Reductor>::restore(P_Chain& A_chain){
  for(int i=this->getReductors().size()-1;i>=0;--i){
    this->getReductors()[i].restore(A_chain,*this);
  }
}
*/



// ************** Skeleton methods for k-sat ************************ //
/************************************************************************************/

// Auxiliary, recursive method for cubicalClosureSkeleton below
template <typename P_EuclSet,typename P_CubCellSetSimplificator>
bool CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::belongsToCubicalClosure(BitCoordIterator& A_it){
  // -- MM  std::cout << "   Pixel " << *A_it << std::endl;
  if(isVertex(A_it)){
    return A_it.getBit();
    // -- MM  std::cout << " A vertex showing " << A_it.getBit() << " found\n";
  }
  bool result=true;
  for(int i=0;i<this->embDim();++i){
    if(A_it[i]%2 != 0){
      A_it.decInDir(i);
      // -- MM  std::cout << "   Testing face " << *A_it << " \n";
      result = A_it.getBit();
      A_it.incInDir(i);
      if(!result) break;
      A_it.incInDir(i);
      // -- MM  std::cout << "   Testing face " << *A_it << " \n";
      result = A_it.getBit();
      A_it.decInDir(i);
      if(!result) break;
    }
  }
  // -- MM  std::cout << "Result is  " << result << " \n";
  return result;
}

/************************************************************************************/

// Given a CubRepSet consisting of vertices only, compute
// the A_skeletonDimension skeleton of the cubical closure
// defined by the recursive formula that a cube belongs to the
// closure if all it faces belong to the closure
// Used in the k-sat project

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
void CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>::cubicalClosureSkeleton(int A_skeletonDimension){
  for(int i=1;i<=A_skeletonDimension;++i){
    BitCoordIterator it(*this);
    // -- MM  int cnt=0;
    for(it=this->begin();it<this->end();++it){
      if(
        it.inSpace() &&
        it.ownDim() == i &&
        belongsToCubicalClosure(it)
      ){
        it.setBit();
        // -- MM  ++cnt;
      }
    }
    // -- MM  std::cout << "         Found " << cnt  << " cells\n";
  }
}

/************************************************************************************/



#endif // _CUBCELLSETT_H_

/// @}

