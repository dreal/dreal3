/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file repSet_ECube.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/repSet/RepSet.hpp"
#include "capd/repSet/ElementaryCube.h"

template RepSet<ElementaryCube>&  RepSet<ElementaryCube>::operator-=(const RepSet<ElementaryCube>&  s);
template RepSet<ElementaryCube>&  RepSet<ElementaryCube>::operator*=(const RepSet<ElementaryCube>&  s);

template bool RepSet<ElementaryCube>::operator<=(const RepSet<ElementaryCube>&  s) const;

template void RepSet<ElementaryCube>::enclosingBox(int minCoords[],int maxCoords[]) const;
template void RepSet<ElementaryCube>::lowerEnclosingBox(int minCoords[],int maxCoords[]) const;

template RepSet<ElementaryCube> operator+ <ElementaryCube>(const RepSet<ElementaryCube>&  s1,const RepSet<ElementaryCube>&  s2);
template RepSet<ElementaryCube> operator- <ElementaryCube>(const RepSet<ElementaryCube>&  s1,const RepSet<ElementaryCube>&  s2);
template RepSet<ElementaryCube> operator* <ElementaryCube>(const RepSet<ElementaryCube>&  s1,const RepSet<ElementaryCube>&  s2);

template std::istream& operator>> <ElementaryCube>(std::istream& inp, RepSet<ElementaryCube>&  A_RepSet);
template std::ostream& operator<< <ElementaryCube>(std::ostream& out, const RepSet<ElementaryCube>&  A_RepSet);
