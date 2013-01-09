
/////////////////////////////////////////////////////////////////////////////
/// @file ZVector.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <iostream>
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Dimension.h"

namespace capd{ 
  namespace vectalg{


template class Vector<int,DIM>;

template Vector<int,DIM> abs<int,DIM> (const Vector<int,DIM> &v);
template Vector<int,DIM> operator- <int,DIM> (const Vector<int,DIM> &v);
template Vector<int,DIM> operator+ <int,DIM> (const Vector<int,DIM> &v1,const Vector<int,DIM> &v2);
template Vector<int,DIM> operator- <int,DIM> (const Vector<int,DIM> &v1,const Vector<int,DIM> &v2);
template int operator* <int,DIM> (const Vector<int,DIM> &v1,const Vector<int,DIM> &v2);

template Vector<int,DIM> operator* <int,int,DIM> (const Vector<int,DIM> &v,const int &s);
template Vector<int,DIM> operator* <int,int,DIM> (const int &s,const Vector<int,DIM> &v);
template Vector<int,DIM> operator/ <int,int,DIM> (const Vector<int,DIM> &v, const int &s);

template Vector<int,DIM> operator* <int,long,DIM>(const Vector<int,DIM> &v,const long &s);
template Vector<int,DIM> operator* <int,long,DIM>(const long &s,const Vector<int,DIM> &v);
template Vector<int,DIM> operator/ <int,long,DIM>(const Vector<int,DIM> &v, const long &s);

template Vector<int,DIM> operator+ <int,DIM> (const Vector<int,DIM> &v,const int &s);
template Vector<int,DIM> operator- <int,DIM> (const Vector<int,DIM> &v,const int &s);
template bool operator < <int,DIM> (const Vector<int,DIM> &v1,const Vector<int,DIM> &v2);
template bool operator > <int,DIM> (const Vector<int,DIM> &v1,const Vector<int,DIM> &v2);
template bool operator<= <int,DIM> (const Vector<int,DIM> &v1,const Vector<int,DIM> &v2);
template bool operator>= <int,DIM> (const Vector<int,DIM> &v1,const Vector<int,DIM> &v2);
template std::ostream &operator<< <int,DIM> (std::ostream &out, const Vector<int,DIM> &v);
template std::istream &operator>> <int,DIM>(std::istream &inp, Vector<int,DIM> &v);

}}  // end of namespace capd::vectalg

