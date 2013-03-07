
/////////////////////////////////////////////////////////////////////////////
/// @file vectalg/DVector.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <iostream>
#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.hpp"

namespace capd{ 
  namespace vectalg{

template class Vector<double,CAPD_DEFAULT_DIMENSION>;

template Vector<double,CAPD_DEFAULT_DIMENSION> abs<double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator- <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator+ <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v1,const Vector<double,CAPD_DEFAULT_DIMENSION> &v2);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator- <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v1,const Vector<double,CAPD_DEFAULT_DIMENSION> &v2);
template double operator* <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v1,const Vector<double,CAPD_DEFAULT_DIMENSION> &v2);

template Vector<double,CAPD_DEFAULT_DIMENSION> operator* <double,double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v,const double &s);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator* <double,double,CAPD_DEFAULT_DIMENSION> (const double &s,const Vector<double,CAPD_DEFAULT_DIMENSION> &v);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator/ <double,double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v, const double &s);

template Vector<double,CAPD_DEFAULT_DIMENSION> operator* <double,long,CAPD_DEFAULT_DIMENSION>(const Vector<double,CAPD_DEFAULT_DIMENSION> &v,const long &s);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator* <double,long,CAPD_DEFAULT_DIMENSION>(const long &s,const Vector<double,CAPD_DEFAULT_DIMENSION> &v);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator/ <double,long,CAPD_DEFAULT_DIMENSION>(const Vector<double,CAPD_DEFAULT_DIMENSION> &v, const long &s);

template Vector<double,CAPD_DEFAULT_DIMENSION> operator* <double,int,CAPD_DEFAULT_DIMENSION>(const Vector<double,CAPD_DEFAULT_DIMENSION> &v,const int &s);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator* <double,int,CAPD_DEFAULT_DIMENSION>(const int &s,const Vector<double,CAPD_DEFAULT_DIMENSION> &v);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator/ <double,int,CAPD_DEFAULT_DIMENSION>(const Vector<double,CAPD_DEFAULT_DIMENSION> &v, const int &s);

template Vector<double,CAPD_DEFAULT_DIMENSION> operator+ <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v,const double &s);
template Vector<double,CAPD_DEFAULT_DIMENSION> operator- <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v,const double &s);
template bool operator < <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v1,const Vector<double,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator > <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v1,const Vector<double,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator<= <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v1,const Vector<double,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator>= <double,CAPD_DEFAULT_DIMENSION> (const Vector<double,CAPD_DEFAULT_DIMENSION> &v1,const Vector<double,CAPD_DEFAULT_DIMENSION> &v2);
template std::ostream &operator<< <double,CAPD_DEFAULT_DIMENSION> (std::ostream &out, const Vector<double,CAPD_DEFAULT_DIMENSION> &v);
template std::istream &operator>> <double,CAPD_DEFAULT_DIMENSION>(std::istream &inp, Vector<double,CAPD_DEFAULT_DIMENSION> &v);

template void subtractObjects<>(const Vector<double,CAPD_DEFAULT_DIMENSION>& v1,const Vector<double,CAPD_DEFAULT_DIMENSION>& v2, Vector<double,CAPD_DEFAULT_DIMENSION>& result);
template void addObjects<>(const Vector<double,CAPD_DEFAULT_DIMENSION>& v1,const Vector<double,CAPD_DEFAULT_DIMENSION>& v2, Vector<double,CAPD_DEFAULT_DIMENSION>& result);

}}  // end of namespace capd::vectalg


