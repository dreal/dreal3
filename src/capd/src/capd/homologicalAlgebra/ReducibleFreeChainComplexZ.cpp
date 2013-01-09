/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ReducibleFreeChainComplexZ.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/*
#include "capd/homologicalAlgebra/FreeModule.h"
#include "capd/homologicalAlgebra/ChainAux.h"
//#include "homologicalAlgebra/SubModule.h"
//#include "homologicalAlgebra/QuotientModule.h"
//#include "homologicalAlgebra/FreeModuleHomomorphism.h"
#include "capd/homologicalAlgebra/FreeChainComplex.h"
*/
#include "capd/vectalg/Vector.h"
using namespace capd::vectalg;
#include "capd/homologicalAlgebra/homologicalAlgebra.h"
#include "capd/repSet/ElementaryCube.h"
#include "capd/repSet/ElementaryCell.h"

#include "capd/homologicalAlgebra/ReducibleFreeChainComplex.hpp"

typedef int GeneratorCode;
typedef FreeModule<GeneratorCode,capd::vectalg::Matrix<int,0,0> > ZFreeModule;



template ReducibleFreeChainComplex<ZFreeModule>::ReducibleFreeChainComplex(const FreeChainComplex<ZFreeModule>&);
template ReducibleFreeChainComplex<ZFreeModule>::ReducibleFreeChainComplex(const std::vector<ElementaryCube>&);
template ReducibleFreeChainComplex<ZFreeModule>::ReducibleFreeChainComplex(const std::set<ElementaryCell>&);
template int ReducibleFreeChainComplex<ZFreeModule>::reduce();
template bool ReducibleFreeChainComplex<ZFreeModule>::removeSimpleHomologyGenerators(std::vector<std::vector<GeneratorCode> >& simpleHomologyGenerators);
template ReducibleFreeChainComplex<ZFreeModule>::operator FreeChainComplex<ZFreeModule>();
template int ReducibleFreeChainComplex<ZFreeModule>::reduceViaLocalSort();
template int ReducibleFreeChainComplex<ZFreeModule>::reduceViaSort();

template std::ostream& operator<< <ZFreeModule>(std::ostream& out,const ReducibleFreeChainComplex<ZFreeModule>&);
