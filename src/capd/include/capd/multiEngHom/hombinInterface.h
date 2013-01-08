/// @addtogroup multiEngHom
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file hombinInterface.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include <stdexcept>
#include "capd/auxil/CRef.h"
#include "capd/homologicalAlgebra/HomologySignature.h"
#include "capd/homology/homology.h"
#include "capd/multiEngHom/powerTwoCeiling.h"

template <typename P_CubSet>
CRef<HomologySignature<int> > homologyViaHombin(CRef<P_CubSet> A_cubSetCR){
fcout << "homologyViaHombin" << std::endl;
std::cout << "homologyViaHombin" << std::endl;
  const typename P_CubSet::BaseClass& euclSet=A_cubSetCR().getBaseObject();
  int dim=euclSet.embDim();
  if(dim!=3) throw std::runtime_error("homologyViaHombin: adaptation only for dimension 3!");
  int maxSize=1;
  for(int i=0;i<dim;++i){
    if(euclSet.getPaddedWidth(i)>maxSize) maxSize=euclSet.getPaddedWidth(i);
fcout << "HombinInterface found unpaddedWidth=" << euclSet.getPaddedWidth(i)  << std::endl;
  }
  if(maxSize<32) maxSize=32;
  maxSize=powerTwoCeiling(maxSize);
fcout << "HombinInterface requested maxSize=" << maxSize  << std::endl;
  typename P_CubSet::BaseClass internal(maxSize,true); // true means clear

  typename P_CubSet::BaseClass::PointCoordIterator it(A_cubSetCR());
  for(it=A_cubSetCR().begin();it<A_cubSetCR().end();++it){
    typename P_CubSet::BaseClass::Pixel c(it.coords());
    internal.addPixel(c);
  }
  char* buf=const_cast<char*>(reinterpret_cast<const char*>(internal.getBaseObject().getBaseObject().getBitmap()));
  int logTwo=baseTwoLog(maxSize);
  std::vector<int> betti(dim + 1);
  switch(logTwo){
    case 10:   capd::homology::ComputeBettiNumbers<3,10,int>(buf, &betti[0]);break;
    case 9:    capd::homology::ComputeBettiNumbers<3,9,int>(buf, &betti[0]);break;
    case 8:    capd::homology::ComputeBettiNumbers<3,8,int>(buf, &betti[0]);break;
    case 7:    capd::homology::ComputeBettiNumbers<3,7,int>(buf, &betti[0]);break;
    case 6:    capd::homology::ComputeBettiNumbers<3,6,int>(buf, &betti[0]);break;
    case 5:    capd::homology::ComputeBettiNumbers<3,5,int>(buf, &betti[0]);break;
    default: throw std::runtime_error("homologyViaHombin: adaptation supports only cube sides in [1,1024]!");
  }
  return CRef<HomologySignature<int> >(new HomologySignature<int> (betti));
}

/// @}

