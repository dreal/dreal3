/// @addtogroup bitSet
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file BitmapUL.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Marian Mrozek 2005-2006
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include "capd/bitSet/BitmapT.hpp"
typedef unsigned long int cluster;

template class BitmapT<cluster>;

template std::istream& operator>> <cluster>(std::istream& in,BitmapT<cluster>&);
template std::ostream& operator<< <cluster>(std::ostream& out,const BitmapT<cluster>&);
