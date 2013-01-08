/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file CrbInclHomology.hpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 
#if !defined(_CRBINCLHOMOLOGY_HPP_)
#define _CRBINCLHOMOLOGY_HPP_

#include "capd/homologicalAlgebra/InclusionHomology.hpp"


std::string CrbIncHom(const char* subFileName,const char* supFileName){

  typedef unsigned long int cluster;
  typedef ECellMDCodeT<cluster,eDim> CubFaceIndexType;
  typedef BitSetT<BitmapT<cluster> > BitSet;
  typedef EuclBitSetT<BitSet,eDim> EuclBitSet;
  typedef CubSetT<EuclBitSet> BCubSet;
  typedef CubCellSetT<EuclBitSet,ReductionPairT<CubFaceIndexType> > SCubCelSet;
  typedef capd::vectalg::Matrix<int,0,0> MatrixType;
  typedef FreeModule<CubFaceIndexType,MatrixType> FreeModuleType;
  typedef FreeChainComplex<FreeModuleType> FreeChainComplexType;



  CRef<SCubCelSet> subCubCellSetCR=readCubCellSet<BCubSet,SCubCelSet>(subFileName);
  CRef<SCubCelSet> supCubCellSetCR=readCubCellSet<BCubSet,SCubCelSet>(supFileName);
  return InclusionHomology<SCubCelSet,FreeChainComplexType>::CrbIncHom(subCubCellSetCR,supCubCellSetCR);
}
#endif //_CRBINCLHOMOLOGY_HPP_

/// @}

