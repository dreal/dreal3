/// @addtogroup homologicalAlgebra
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file FreeChainComplexZ.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/homologicalAlgebra/homologicalAlgebra.h"
#include "capd/repSet/ElementaryCube.h"
#include "capd/repSet/ElementaryCell.h"

#include "capd/homologicalAlgebra/FreeChainComplex.hpp"

typedef FreeModule<int,capd::vectalg::Matrix<int,0,0> > ZFreeModule;


template class FreeChainComplex<ZFreeModule>;

template std::ostream& operator<< <ZFreeModule>(std::ostream& out,const FreeChainComplex<ZFreeModule>&);
