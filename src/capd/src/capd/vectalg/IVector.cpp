
/////////////////////////////////////////////////////////////////////////////
/// @file IVector.cpp
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
#include "capd/interval/lib.h"

namespace capd{ 
  namespace vectalg{


template class Vector<Interval,DIM>;

template Vector<Interval,DIM> abs<Interval,DIM> (const Vector<Interval,DIM> &v);
template Vector<Interval,DIM> operator- <Interval,DIM> (const Vector<Interval,DIM> &v);
template Vector<Interval,DIM> operator+ <Interval,DIM>(const Vector<Interval,DIM> &v1,const Vector<Interval,DIM> &v2);
template Vector<Interval,DIM> operator- <Interval,DIM>(const Vector<Interval,DIM> &v1,const Vector<Interval,DIM> &v2);
template Interval operator* <Interval,DIM> (const Vector<Interval,DIM> &v1,const Vector<Interval,DIM> &v2);

template Vector<Interval,DIM> operator* <Interval,Interval,DIM>(const Vector<Interval,DIM> &v,const Interval &s);
template Vector<Interval,DIM> operator* <Interval,Interval,DIM>(const Interval &s,const Vector<Interval,DIM> &v);
template Vector<Interval,DIM> operator/ <Interval,Interval,DIM>(const Vector<Interval,DIM> &v, const Interval &s);

template Vector<Interval,DIM> operator* <Interval,double,DIM>(const Vector<Interval,DIM> &v,const double &s);
template Vector<Interval,DIM> operator* <Interval,double,DIM>(const double &s,const Vector<Interval,DIM> &v);
template Vector<Interval,DIM> operator/ <Interval,double,DIM>(const Vector<Interval,DIM> &v, const double &s);

template Vector<Interval,DIM> operator* <Interval,long,DIM>(const Vector<Interval,DIM> &v,const long &s);
template Vector<Interval,DIM> operator* <Interval,long,DIM>(const long &s,const Vector<Interval,DIM> &v);
template Vector<Interval,DIM> operator/ <Interval,long,DIM>(const Vector<Interval,DIM> &v, const long &s);

template Vector<Interval,DIM> operator* <Interval,int,DIM>(const Vector<Interval,DIM> &v,const int &s);
template Vector<Interval,DIM> operator* <Interval,int,DIM>(const int &s,const Vector<Interval,DIM> &v);
template Vector<Interval,DIM> operator/ <Interval,int,DIM>(const Vector<Interval,DIM> &v, const int &s);

template Vector<Interval,DIM> operator+ <Interval,DIM> (const Vector<Interval,DIM> &v, const Interval &s);
template Vector<Interval,DIM> operator- <Interval,DIM>(const Vector<Interval,DIM> &v,const Interval &s);
template bool operator < <Interval,DIM> (const Vector<Interval,DIM> &v1,const Vector<Interval,DIM> &v2);
template bool operator > <Interval,DIM> (const Vector<Interval,DIM> &v1,const Vector<Interval,DIM> &v2);
template bool operator<= <Interval,DIM> (const Vector<Interval,DIM> &v1,const Vector<Interval,DIM> &v2);
template bool operator>= <Interval,DIM> (const Vector<Interval,DIM> &v1,const Vector<Interval,DIM> &v2);
template std::ostream &operator<< <Interval,DIM> (std::ostream &out, const Vector<Interval,DIM> &v);
template std::istream &operator>> <Interval,DIM>(std::istream &inp, Vector<Interval,DIM> &v);



typedef Vector<Interval,DIM> IVector;

template IVector intervalHull<IVector>(const IVector &A, const IVector &B);
template void split<IVector>(IVector& v, IVector& rv);
template IVector midVector<IVector>(const IVector& v);
template IVector leftVector<IVector>(const IVector& v);
template IVector rightVector<IVector>(const IVector& v);
template Interval size<IVector>(const IVector& v);
template IVector diam<IVector>(const IVector& v);
template IVector intervalBall<IVector>(const IVector &iv, const Interval &r);
template Interval solveAffineInclusion<IVector>(const IVector& a,const IVector& p,const IVector& c);
template Interval solveAffineInclusion<IVector>(const IVector& a,const IVector& p,const IVector& c,int&);
template bool subset<IVector>(const IVector& v1, const IVector& v2);
template bool subsetInterior<IVector>(const IVector& v1, const IVector& v2);
template IVector intersection<IVector>(const IVector &v1, const IVector &v2);

}}  // end of namespace capd::vectalg

