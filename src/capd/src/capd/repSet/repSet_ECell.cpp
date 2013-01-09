/// @addtogroup repSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file repSet_ECell.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/repSet/RepSet.hpp"
#include "capd/repSet/ElementaryCell.h"

template RepSet<ElementaryCell>&  RepSet<ElementaryCell>::operator-=(const RepSet<ElementaryCell>&  s);
template RepSet<ElementaryCell>&  RepSet<ElementaryCell>::operator*=(const RepSet<ElementaryCell>&  s);

template bool RepSet<ElementaryCell>::operator<=(const RepSet<ElementaryCell>&  s) const;

template void RepSet<ElementaryCell>::enclosingBox(int minCoords[],int maxCoords[]) const;
template void RepSet<ElementaryCell>::lowerEnclosingBox(int minCoords[],int maxCoords[]) const;

template RepSet<ElementaryCell> operator+ <ElementaryCell>(const RepSet<ElementaryCell>&  s1,const RepSet<ElementaryCell>&  s2);
template RepSet<ElementaryCell> operator- <ElementaryCell>(const RepSet<ElementaryCell>&  s1,const RepSet<ElementaryCell>&  s2);
template RepSet<ElementaryCell> operator* <ElementaryCell>(const RepSet<ElementaryCell>&  s1,const RepSet<ElementaryCell>&  s2);

template std::istream& operator>> <ElementaryCell>(std::istream& inp, RepSet<ElementaryCell>&  A_RepSet);
template std::ostream& operator<< <ElementaryCell>(std::ostream& out, const RepSet<ElementaryCell>&  A_RepSet);
