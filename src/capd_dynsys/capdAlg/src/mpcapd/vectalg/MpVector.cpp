
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


template class Vector<MpFloat,CAPD_DEFAULT_DIMENSION>;

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> abs<MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator- <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator+ <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v2);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator- <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v2);
template MpFloat operator* <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v2);

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v,const MpFloat &s);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,MpFloat,CAPD_DEFAULT_DIMENSION> (const MpFloat &s,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator/ <MpFloat,MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v, const MpFloat &s);

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,long,CAPD_DEFAULT_DIMENSION>(const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v,const long &s);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,long,CAPD_DEFAULT_DIMENSION>(const long &s,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator/ <MpFloat,long,CAPD_DEFAULT_DIMENSION>(const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v, const long &s);

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,int,CAPD_DEFAULT_DIMENSION>(const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v,const int &s);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator* <MpFloat,int,CAPD_DEFAULT_DIMENSION>(const int &s,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator/ <MpFloat,int,CAPD_DEFAULT_DIMENSION>(const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v, const int &s);

template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator+ <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v,const MpFloat &s);
template Vector<MpFloat,CAPD_DEFAULT_DIMENSION> operator- <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v,const MpFloat &s);
template bool operator < <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator > <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator<= <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v2);
template bool operator>= <MpFloat,CAPD_DEFAULT_DIMENSION> (const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v2);
template std::ostream &operator<< <MpFloat,CAPD_DEFAULT_DIMENSION> (std::ostream &out, const Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v);
template std::istream &operator>> <MpFloat,CAPD_DEFAULT_DIMENSION>(std::istream &inp, Vector<MpFloat,CAPD_DEFAULT_DIMENSION> &v);

template void subtractObjects<>(const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>& v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>& v2, Vector<MpFloat,CAPD_DEFAULT_DIMENSION>& result);
template void addObjects<>(const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>& v1,const Vector<MpFloat,CAPD_DEFAULT_DIMENSION>& v2, Vector<MpFloat,CAPD_DEFAULT_DIMENSION>& result);

}}  // end of namespace capd::vectalg

#endif // __HAVE_MPFR__
