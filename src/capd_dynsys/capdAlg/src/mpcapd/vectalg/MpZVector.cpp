
/////////////////////////////////////////////////////////////////////////////
/// @file mpcapd/vectalg/MpVector.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifdef __HAVE_MPFR__

#include <iostream>
#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/mplib.h"

namespace capd{ 
  namespace vectalg{


template class Vector<MpInt,CAPD_DEFAULT_DIMENSION>;

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> abs<MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator- <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator+ <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v2);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator- <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v2);
template MpInt operator* <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v2);

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator* <MpInt,MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v,const MpInt &s);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator* <MpInt,MpInt,CAPD_DEFAULT_DIMENSION> (const MpInt &s,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator/ <MpInt,MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v, const MpInt &s);

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator* <MpInt,long,CAPD_DEFAULT_DIMENSION>(const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v,const long &s);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator* <MpInt,long,CAPD_DEFAULT_DIMENSION>(const long &s,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator/ <MpInt,long,CAPD_DEFAULT_DIMENSION>(const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v, const long &s);

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator* <MpInt,int,CAPD_DEFAULT_DIMENSION>(const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v,const int &s);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator* <MpInt,int,CAPD_DEFAULT_DIMENSION>(const int &s,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator/ <MpInt,int,CAPD_DEFAULT_DIMENSION>(const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v, const int &s);

template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator+ <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v,const MpInt &s);
template Vector<MpInt,CAPD_DEFAULT_DIMENSION> operator- <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v,const MpInt &s);
template bool operator < <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator > <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator<= <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator>= <MpInt,CAPD_DEFAULT_DIMENSION> (const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v2);
template std::ostream &operator<< <MpInt,CAPD_DEFAULT_DIMENSION> (std::ostream &out, const Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v);
template std::istream &operator>> <MpInt,CAPD_DEFAULT_DIMENSION>(std::istream &inp, Vector<MpInt,CAPD_DEFAULT_DIMENSION> &v);

template void subtractObjects<>(const Vector<MpInt,CAPD_DEFAULT_DIMENSION>& v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION>& v2, Vector<MpInt,CAPD_DEFAULT_DIMENSION>& result);
template void addObjects<>(const Vector<MpInt,CAPD_DEFAULT_DIMENSION>& v1,const Vector<MpInt,CAPD_DEFAULT_DIMENSION>& v2, Vector<MpInt,CAPD_DEFAULT_DIMENSION>& result);

}}  // end of namespace capd::vectalg

#endif // __HAVE_MPFR__
