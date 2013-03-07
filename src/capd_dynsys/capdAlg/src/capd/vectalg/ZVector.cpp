
/////////////////////////////////////////////////////////////////////////////
/// @file vectalg/ZVector.cpp
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


template class Vector<int,CAPD_DEFAULT_DIMENSION>;

template Vector<int,CAPD_DEFAULT_DIMENSION> abs<int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v);
template Vector<int,CAPD_DEFAULT_DIMENSION> operator- <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v);
template Vector<int,CAPD_DEFAULT_DIMENSION> operator+ <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v1,const Vector<int,CAPD_DEFAULT_DIMENSION> &v2);
template Vector<int,CAPD_DEFAULT_DIMENSION> operator- <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v1,const Vector<int,CAPD_DEFAULT_DIMENSION> &v2);
template int operator* <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v1,const Vector<int,CAPD_DEFAULT_DIMENSION> &v2);

template Vector<int,CAPD_DEFAULT_DIMENSION> operator* <int,int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v,const int &s);
template Vector<int,CAPD_DEFAULT_DIMENSION> operator* <int,int,CAPD_DEFAULT_DIMENSION> (const int &s,const Vector<int,CAPD_DEFAULT_DIMENSION> &v);
template Vector<int,CAPD_DEFAULT_DIMENSION> operator/ <int,int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v, const int &s);

template Vector<int,CAPD_DEFAULT_DIMENSION> operator* <int,long,CAPD_DEFAULT_DIMENSION>(const Vector<int,CAPD_DEFAULT_DIMENSION> &v,const long &s);
template Vector<int,CAPD_DEFAULT_DIMENSION> operator* <int,long,CAPD_DEFAULT_DIMENSION>(const long &s,const Vector<int,CAPD_DEFAULT_DIMENSION> &v);
template Vector<int,CAPD_DEFAULT_DIMENSION> operator/ <int,long,CAPD_DEFAULT_DIMENSION>(const Vector<int,CAPD_DEFAULT_DIMENSION> &v, const long &s);

template Vector<int,CAPD_DEFAULT_DIMENSION> operator+ <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v,const int &s);
template Vector<int,CAPD_DEFAULT_DIMENSION> operator- <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v,const int &s);
template bool operator < <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v1,const Vector<int,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator > <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v1,const Vector<int,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator<= <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v1,const Vector<int,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator>= <int,CAPD_DEFAULT_DIMENSION> (const Vector<int,CAPD_DEFAULT_DIMENSION> &v1,const Vector<int,CAPD_DEFAULT_DIMENSION> &v2);
template std::ostream &operator<< <int,CAPD_DEFAULT_DIMENSION> (std::ostream &out, const Vector<int,CAPD_DEFAULT_DIMENSION> &v);
template std::istream &operator>> <int,CAPD_DEFAULT_DIMENSION>(std::istream &inp, Vector<int,CAPD_DEFAULT_DIMENSION> &v);

template void subtractObjects<>(const Vector<int,CAPD_DEFAULT_DIMENSION>& v1,const Vector<int,CAPD_DEFAULT_DIMENSION>& v2, Vector<int,CAPD_DEFAULT_DIMENSION>& result);
template void addObjects<>(const Vector<int,CAPD_DEFAULT_DIMENSION>& v1,const Vector<int,CAPD_DEFAULT_DIMENSION>& v2, Vector<int,CAPD_DEFAULT_DIMENSION>& result);

}}  // end of namespace capd::vectalg

