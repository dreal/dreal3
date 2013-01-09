/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CubSetT.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.





#ifndef _CAPD_BITSET_CUBSETT_H_
#define _CAPD_BITSET_CUBSETT_H_

#include <vector>
#include "capd/repSet/RepSet.h"
#include "capd/repSet/ElementaryCube.h"
#include "capd/homologicalAlgebra/cubSetFunctors.hpp"

using std::vector;

template <typename P_EuclSet,typename P_CubCellSetSimplificator>
class CubCellSetT;

template <typename P_EuclSet>
class CubSetT : public P_EuclSet{
protected:

  typedef typename P_EuclSet::PixelNeighborOffset PixelNeighborOffset;

public:
  typedef typename P_EuclSet::Pixel Pixel;
  typedef typename P_EuclSet::BitCoordIterator BitCoordIterator;
  typedef typename P_EuclSet::BitIterator BitIterator;
  typedef typename P_EuclSet::PointIterator PointIterator;
  typedef typename P_EuclSet::WordIterator WordIterator;
  typedef typename P_EuclSet::PointCoordIterator PointCoordIterator;
  typedef typename P_EuclSet::NeighbIterator NeighbIterator;

  typedef bool (CubSetT::*BoolBCI_Ptr)(const BitCoordIterator& it) const;
  typedef bool (CubSetT::*BoolBI_Ptr)(const BitIterator& it) const;
  typedef CubSetT& (CubSetT::*CubSetT_void_Ptr)();
  typedef int (CubSetT::*CubSetT_CubSetT_Ptr)(CubSetT&) const;
//  typedef CubSetT& (CubSetT::*CubSetT_void_Ptr)(); // see 2 lines above



//  typedef typename P_EuclSet::BdNeighbIterator BdNeighbIterator;  // BdNeighbIterator does not work correctly yet
  typedef P_EuclSet BaseClass;

  // the following constatnts are used in neighbAcyclicLT
  // in the construction of the neighborhood signature in dimensions 1,2 and 3
  static const unsigned int midBit=13;          // this constant for dim=3 is used in dim 1 and 2 as well
  static const unsigned mask= (1 << midBit)-1;


  static BoolBCI_Ptr neighbAcyclicBCI; // Pointer to neighbAcyclic() via BitCoordIterator(s)
  static BoolBI_Ptr neighbAcyclicBI;   // Pointer to neighbAcyclic() via BitIterator(s)

  using P_EuclSet::Length;

  explicit CubSetT(int size=0):P_EuclSet(size,true){}   // BitmapT with size pixels in each dimension
  explicit CubSetT(const int* w):P_EuclSet(w,true){} // BitmapT with w[i] pixels in dimension i
  explicit CubSetT(const int* w, const char* bytes):P_EuclSet(w,bytes){} // BitmapT with w[i] pixels in dimension i, using a provided bitmap
  CubSetT(const CubSetT& org, bool clear=false):P_EuclSet(org,clear){}
  CubSetT(const CubSetT& org, const std::vector<int>& lc, const std::vector<int>& uc):P_EuclSet(org,lc,uc){}
  CubSetT(const CubSetT& org,const Pixel& lc,const Pixel& uc):P_EuclSet(org,lc,uc){}
  CubSetT(const RepSet<ElementaryCube>& A_RepSetOfElementaryCube):P_EuclSet(A_RepSetOfElementaryCube){}

  template<typename P_CubCellSetSimplificator>
  CubSetT(const CubCellSetT<P_EuclSet,P_CubCellSetSimplificator>& org):P_EuclSet(*reinterpret_cast<const P_EuclSet*>(&org)){}

  const P_EuclSet& getBaseObject() const{ return *static_cast<const P_EuclSet*>(this);}
  const int embDim() const{ return P_EuclSet::embDim();}

  void getNeighbors(const Pixel& p, vector<Pixel>& neighbors) const;
  void getNeighborhood3(const Pixel& p, CubSetT& neighborhood) const;
  void getNeighborhood5(const Pixel& p, CubSetT& neighborhood) const;
  int neighbSignature(const BitIterator& it) const;

  bool neighbAcyclicLT(const BitIterator& it) const;
  bool neighbAcyclicLT(const BitIterator& it,int& count) const;
  bool neighbAcyclicSI_BI(const BitIterator& it) const;  // suffix _BI: gcc fails to recognize properly overloaded functions under function pointer assignment!!!

  bool neighbAcyclicLT_BCI(const BitCoordIterator& it) const; // suffix _BCI: gcc fails to recognize properly overloaded functions under function pointer assignment!!!
  bool neighbAcyclicHOM(const BitCoordIterator& it) const;
  bool neighbAcyclicOSSI(const BitCoordIterator& it) const;
  bool neighbAcyclicSI(const BitCoordIterator& it) const;
  bool neighbAcyclicSIR(const BitCoordIterator& it) const;
//--  bool (CubSetT::*neighbAcyclic)(const BitCoordIterator& it) const = &CubSetT::neighbAcyclicSI;

  void addEmptyCollar();

  CubSetT& expandToComponentOf(const Pixel& p, /* in */ const CubSetT& set2);
  CubSetT& expandToComponentOf(const Pixel& p, /* in */ const CubSetT& set2, Pixel& lc, Pixel& uc);
  bool extractComponent(CubSetT& component,CubSetT& rest);
  bool extractComponent(CubSetT& component,CubSetT& rest, Pixel& lc, Pixel& uc);
  int decomposeToComponents(std::vector<CubSetT >& components) const;
  CubSetT& expandToComponentOf(const CubSetT& set2);

  CubSetT& shaveBCI(); // Based on BitCoordIterator
  CubSetT& shaveBI();
//  CubSetT& shave(){return shaveBCI();}
  CubSetT& shave();
  CubSetT& shaveWithFixedSubset(const CubSetT& A_subset); // Added for persistence computation in 3d


  int simpleIntersection(vector<Pixel> pixels) const;
  int acyclicSubspaceBCI(CubSetT& acSubsp) const;   // Based on BitCoordIterator
  int acyclicSubspaceBI(CubSetT& acSubsp) const;    // Based on BitIterator (faster)
  int acyclicSubspaceOrg(CubSetT& acSubsp) const;    // Original acyclic subspace method
  int acyclicSubspace(CubSetT& acSubsp) const{return acyclicSubspaceBCI(acSubsp);}

  friend void swap(CubSetT& A_set1,CubSetT& A_set2){
    swap(*static_cast<P_EuclSet*>(&A_set1),*static_cast<P_EuclSet*>(&A_set2));
  }
};

/************************************************************************************/

template <typename P_EuclSet>
typename CubSetT<P_EuclSet>::BoolBCI_Ptr CubSetT<P_EuclSet>::neighbAcyclicBCI(&CubSetT<P_EuclSet>::neighbAcyclicSI);

template <typename P_EuclSet>
typename CubSetT<P_EuclSet>::BoolBI_Ptr CubSetT<P_EuclSet>::neighbAcyclicBI(&CubSetT<P_EuclSet>::neighbAcyclicLT);

/************************************************************************************/

#endif // _CAPD_BITSET_CUBSETT_H_

/// @}

