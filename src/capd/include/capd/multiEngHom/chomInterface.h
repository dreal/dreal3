/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file chomInterface.h
///
/// @author Natalia Zaremba, Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) The CAPD Group 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.


// ********** Interface to the chom package by B. Kalies ********** //
/***
     Conversion from EuclBitSetT used in this
     package to bitcodes used in Kalies' programs
***/
#include <limits>
#include <climits>
#include <list>
#include <cmath>
#include <sstream>
#include <exception>
#include "capd/auxil/CRef.h"
#include "capd/homologicalAlgebra/HomologySignature.h"
#include "capd/multiEngHom/powerTwoCeiling.h"
#include "capd/bitSet/BitmapT.h"
#include "capd/bitSet/BitSetT.h"
#include "capd/bitSet/EuclBitSetT.h"
#include "capd/bitSet/CubSetT.h"
#include "capd/bitSet/CubCellSetT.h"

#include "capd/chom/chom_lu.hpp"
#include "capd/chom/list.hpp"
#include "capd/chom/bitcodes.hpp"
#include "capd/chom/cell.hpp"
#include "capd/chom/edge.hpp"
#include "capd/chom/vertex.hpp"
#include "capd/chom/ncell.hpp"
#include "capd/chom/block.hpp"
#include "capd/chom/complex.hpp"
#include "capd/chom/dim.hpp"



/*************** converting EuclBitSetT to a string file in the format of Kalies package ****/
template <typename P_CubSet>
void writeBitcodeCubSet(P_CubSet const& set,ostringstream& setString){
  int dim=set.embDim();
  std::vector<int> minCoord(dim); // min coordinates of the enclosing box
  std::vector<int> maxCoord(dim); // max coordinates of the enclosing box

  // find minCoord and maxCoord
  for(int i=0;i<dim;++i){
    maxCoord[i]=0;
    minCoord[i]=INT_MAX;
  }
  for(typename P_CubSet::PointCoordIterator it=set.begin();it<set.end();++it){
    for(int d=0;d<dim;++d){
     if(it[d]<=minCoord[d]) minCoord[d]=it[d];
     if(it[d]+1>=maxCoord[d]) maxCoord[d]=it[d]+1;
    }
  }

  int boxSizeAux=0; // maximal length of the enclosing box sides
  for(int i=0;i<dim;++i){
    if (maxCoord[i]-minCoord[i]>boxSizeAux) boxSizeAux=(maxCoord[i]-minCoord[i]);
  }
  int depth=1;   // depth needed to store all coordinates
  int boxSize=1; // minimal power of 2 > boxSizeAux
  while(boxSize<boxSizeAux){
    boxSize*=2;
    ++depth;
  }

  //pomocnicza lista z lizcbami repr pol punktow- do ewentualnego sortowania
  vector<string> bitcodes;

  setString << dim << endl;
  setString << dim*depth << endl;
  setString << set.cardinality() << endl;

  // for every point in the bitmap
  for(typename P_CubSet::PointCoordIterator it=set.begin();it<set.end();++it){
    ostringstream bitcodeStream; // this will contain the bitcode representation of the point
    std::vector<int>  relCoord(dim);           // we need coordinates relative to minCoord
    for(int d=0;d<dim;++d){
      relCoord[d]=it[d]-minCoord[d];
    }

    // mask is used to pick up bits from the coordinates, starting from the top bit, i.e. from the lowest depth

    for(int mask = (int(1) << (depth-1));
    mask >=1;
    mask /= 2 ){
      // write the group of d bits for fixed depth
      for(int d=0;d<dim;++d){
        bitcodeStream << " " << ( (relCoord[d] & mask) != 0);
      }
    }
    // bitcode of the point is ready, push it to the vector
    bitcodes.push_back(bitcodeStream.str());
  }
  // bitcodes must be sorted
  sort(bitcodes.begin(),bitcodes.end());

  // write all bitcodes
  for(int i=0;i<(int)bitcodes.size();++i){
    setString << bitcodes[i] << endl;
  }
}//writeBitcodeCubSet

extern int top_leaf;

int PrepRead(istringstream& in){
   int dim;
   in >> dim;
   if(dim>MAX_CHOM_DIM) throw std::runtime_error("homologyViaChom: cubset dimension inconsistent with MAX_CHOM_DIM from chom package!");
//   if (dim!=DIM){
//      throw std::string("chom: Dimension of the cubset is different from the compiled dimension");
//   }
   in >> cube_bits;
   in >> top_leaf;
   return dim;
}


block* Read(complex* c, istringstream& in){
   int bit;
   block* b=new block(cube_bits,c);
   for (char j=0; j<cube_bits; ++j){
     in >> bit;
     BC(b)(cube_bits-j-1,bit);
   }
   b->CreateCells(c);
   return(b);
}


// Adaptation via istringstream files
// This adaptation is faster and can treat larger files
template <typename P_CubSet>
CRef<HomologySignature<int> > homologyViaChomPackageStreamed(CRef<P_CubSet> A_cubSetCR){
  ostringstream sOut;
  try{
    writeBitcodeCubSet(A_cubSetCR(),sOut);
  }catch(std::bad_alloc){
    throw std::runtime_error("No memory to prepare data for chom package\n");
  }
  istringstream in(sOut.str());

   cube_bits=0;
   top_leaf=0;
   GEN_TOL=0;

   chomDIM=PrepRead(in);;
   for(int i=0; i<chomDIM+1; ++i) gen_flag[i]=0;

   ofstream* gout=NULL;
   block* nb=new block;
   complex c(nb);

   block* b;
   for (int i=0; i<top_leaf; ++i){
     b=Read(&c,in);
     c.InsertCube(b);
   }

   c.FinalCube();
   std::vector<int> betti(chomDIM + 1);
   c.Homology(gout, &betti[0]);

  return CRef<HomologySignature<int> >(new HomologySignature<int> (betti));
}

template <typename P_CubSet>
CRef<HomologySignature<int> > homologyViaChomPackageStreamedCel(CRef<CubCellSetT<typename P_CubSet::BaseClass> > A_cubCellSetCR){
  CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()));
  A_cubCellSetCR().~CubCellSetT<typename P_CubSet::BaseClass>();
  return homologyViaChomPackageStreamed<P_CubSet>(cubSetCR);
}

extern int SUBDIVISIONS;

// Adaptation via Marcio's bitmaps
// This one actually is better than the above only in the 3 dim version with shaving via lookup tables given below
template <typename P_CubSet>
CRef<HomologySignature<int> > homologyViaChomPackage(CRef<P_CubSet> A_cubSetCR){
  const typename P_CubSet::BaseClass& euclSet=A_cubSetCR().getBaseObject();
  int dim=euclSet.embDim();
//  if(dim!=DIM) throw std::runtime_error("homologyViaChom: cubset dimension inconsistent with DIM from chom package!");
  if(dim>MAX_CHOM_DIM) throw std::runtime_error("homologyViaChom: cubset dimension inconsistent with MAX_CHOM_DIM from chom package!");
  chomDIM=dim;
  int maxSize=1;
  for(int i=0;i<dim;++i){
    if(euclSet.getPaddedWidth(i)>maxSize) maxSize=euclSet.getPaddedWidth(i);
  }
  maxSize=powerTwoCeiling(maxSize);
  typename P_CubSet::BaseClass internal(maxSize,true); // true means clear

  typename P_CubSet::BaseClass::PointCoordIterator it(A_cubSetCR());
  for(it=A_cubSetCR().begin();it<A_cubSetCR().end();++it){
    typename P_CubSet::BaseClass::Pixel c(it.coords());
    internal.addPixel(c);
  }
  char* buf=const_cast<char*>(reinterpret_cast<const char*>(internal.getBaseObject().getBaseObject().getBitmap()));
  std::vector<int> betti(dim + 1);

  SUBDIVISIONS=baseTwoLog(maxSize);

  ulong* maxSizes=new ulong[chomDIM];
  for(int i=0;i<dim;++i){
    maxSizes[i]=maxSize;
  }

  compute_homology(buf, maxSizes, &betti[0]); /* Compute Homology */
  delete maxSizes;

  return CRef<HomologySignature<int> >(new HomologySignature<int> (betti));
}

template <typename P_CubSet>
CRef<HomologySignature<int> > homologyViaChomPackageCel(CRef<CubCellSetT<typename P_CubSet::BaseClass> > A_cubCellSetCR){
  CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()) );
  return homologyViaChomPackage<P_CubSet>(cubSetCR);
}

// Adaptation via Marcio's bitmaps with shaving
template <typename P_CubSet>
CRef<HomologySignature<int> > homologyViaChomPackageLT(CRef<P_CubSet> A_cubSetCR){
  const typename P_CubSet::BaseClass& euclSet=A_cubSetCR().getBaseObject();
  int dim=euclSet.embDim();
  if(dim!=3) throw std::runtime_error("homologyViaChomLT: adaptation only for dimension 3!");
  chomDIM=dim;
  if(dim>MAX_CHOM_DIM) throw std::runtime_error("homologyViaChom: cubset dimension inconsistent with MAX_CHOM_DIM from chom package!");
  int maxSize=1;
  for(int i=0;i<dim;++i){
    if(euclSet.getPaddedWidth(i)>maxSize) maxSize=euclSet.getPaddedWidth(i);
  }
  maxSize=powerTwoCeiling(maxSize);
  typename P_CubSet::BaseClass internal(maxSize,true); // true means clear

  typename P_CubSet::BaseClass::PointCoordIterator it(A_cubSetCR());
  for(it=A_cubSetCR().begin();it<A_cubSetCR().end();++it){
    typename P_CubSet::BaseClass::Pixel c(it.coords());
    internal.addPixel(c);
  }
  char* buf=const_cast<char*>(reinterpret_cast<const char*>(internal.getBaseObject().getBaseObject().getBitmap()));
  std::vector<int> betti(dim + 1);

  reduce(buf, maxSize, maxSize, maxSize);  /* Reduce cubical complex */

  SUBDIVISIONS=baseTwoLog(maxSize);
  compute_homology(buf, maxSize, maxSize, maxSize, &betti[0]); /* Compute Homology */

  return CRef<HomologySignature<int> >(new HomologySignature<int> (betti));
}

template <typename P_CubSet>
CRef<HomologySignature<int> > homologyViaChomPackageLTCel(CRef<CubCellSetT<typename P_CubSet::BaseClass> > A_cubCellSetCR){
  CRef<P_CubSet> cubSetCR(new P_CubSet(A_cubCellSetCR()) );
  return homologyViaChomPackageLT<P_CubSet>(cubSetCR);
}


/// @}

