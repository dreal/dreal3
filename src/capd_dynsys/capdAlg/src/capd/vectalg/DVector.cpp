
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

template class Vector<double,DIM>;

template Vector<double,DIM> abs<double,DIM> (const Vector<double,DIM> &v);
template Vector<double,DIM> operator- <double,DIM> (const Vector<double,DIM> &v);
template Vector<double,DIM> operator+ <double,DIM> (const Vector<double,DIM> &v1,const Vector<double,DIM> &v2);
template Vector<double,DIM> operator- <double,DIM> (const Vector<double,DIM> &v1,const Vector<double,DIM> &v2);
template double operator* <double,DIM> (const Vector<double,DIM> &v1,const Vector<double,DIM> &v2);

template Vector<double,DIM> operator* <double,double,DIM> (const Vector<double,DIM> &v,const double &s);
template Vector<double,DIM> operator* <double,double,DIM> (const double &s,const Vector<double,DIM> &v);
template Vector<double,DIM> operator/ <double,double,DIM> (const Vector<double,DIM> &v, const double &s);

template Vector<double,DIM> operator* <double,long,DIM>(const Vector<double,DIM> &v,const long &s);
template Vector<double,DIM> operator* <double,long,DIM>(const long &s,const Vector<double,DIM> &v);
template Vector<double,DIM> operator/ <double,long,DIM>(const Vector<double,DIM> &v, const long &s);

template Vector<double,DIM> operator* <double,int,DIM>(const Vector<double,DIM> &v,const int &s);
template Vector<double,DIM> operator* <double,int,DIM>(const int &s,const Vector<double,DIM> &v);
template Vector<double,DIM> operator/ <double,int,DIM>(const Vector<double,DIM> &v, const int &s);

template Vector<double,DIM> operator+ <double,DIM> (const Vector<double,DIM> &v,const double &s);
template Vector<double,DIM> operator- <double,DIM> (const Vector<double,DIM> &v,const double &s);
template bool operator < <double,DIM> (const Vector<double,DIM> &v1,const Vector<double,DIM> &v2);
template bool operator > <double,DIM> (const Vector<double,DIM> &v1,const Vector<double,DIM> &v2);
template bool operator<= <double,DIM> (const Vector<double,DIM> &v1,const Vector<double,DIM> &v2);
template bool operator>= <double,DIM> (const Vector<double,DIM> &v1,const Vector<double,DIM> &v2);
template std::ostream &operator<< <double,DIM> (std::ostream &out, const Vector<double,DIM> &v);
template std::istream &operator>> <double,DIM>(std::istream &inp, Vector<double,DIM> &v);

template void subtractObjects<>(const Vector<double,DIM>& v1,const Vector<double,DIM>& v2, Vector<double,DIM>& result);
template void addObjects<>(const Vector<double,DIM>& v1,const Vector<double,DIM>& v2, Vector<double,DIM>& result);

}}  // end of namespace capd::vectalg


