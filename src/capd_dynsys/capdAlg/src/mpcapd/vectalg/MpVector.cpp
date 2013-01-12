
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


template class Vector<MpFloat,DIM>;

template Vector<MpFloat,DIM> abs<MpFloat,DIM> (const Vector<MpFloat,DIM> &v);
template Vector<MpFloat,DIM> operator- <MpFloat,DIM> (const Vector<MpFloat,DIM> &v);
template Vector<MpFloat,DIM> operator+ <MpFloat,DIM> (const Vector<MpFloat,DIM> &v1,const Vector<MpFloat,DIM> &v2);
template Vector<MpFloat,DIM> operator- <MpFloat,DIM> (const Vector<MpFloat,DIM> &v1,const Vector<MpFloat,DIM> &v2);
template MpFloat operator* <MpFloat,DIM> (const Vector<MpFloat,DIM> &v1,const Vector<MpFloat,DIM> &v2);

template Vector<MpFloat,DIM> operator* <MpFloat,MpFloat,DIM> (const Vector<MpFloat,DIM> &v,const MpFloat &s);
template Vector<MpFloat,DIM> operator* <MpFloat,MpFloat,DIM> (const MpFloat &s,const Vector<MpFloat,DIM> &v);
template Vector<MpFloat,DIM> operator/ <MpFloat,MpFloat,DIM> (const Vector<MpFloat,DIM> &v, const MpFloat &s);

template Vector<MpFloat,DIM> operator* <MpFloat,long,DIM>(const Vector<MpFloat,DIM> &v,const long &s);
template Vector<MpFloat,DIM> operator* <MpFloat,long,DIM>(const long &s,const Vector<MpFloat,DIM> &v);
template Vector<MpFloat,DIM> operator/ <MpFloat,long,DIM>(const Vector<MpFloat,DIM> &v, const long &s);

template Vector<MpFloat,DIM> operator* <MpFloat,int,DIM>(const Vector<MpFloat,DIM> &v,const int &s);
template Vector<MpFloat,DIM> operator* <MpFloat,int,DIM>(const int &s,const Vector<MpFloat,DIM> &v);
template Vector<MpFloat,DIM> operator/ <MpFloat,int,DIM>(const Vector<MpFloat,DIM> &v, const int &s);

template Vector<MpFloat,DIM> operator+ <MpFloat,DIM> (const Vector<MpFloat,DIM> &v,const MpFloat &s);
template Vector<MpFloat,DIM> operator- <MpFloat,DIM> (const Vector<MpFloat,DIM> &v,const MpFloat &s);
template bool operator < <MpFloat,DIM> (const Vector<MpFloat,DIM> &v1,const Vector<MpFloat,DIM> &v2);
template bool operator > <MpFloat,DIM> (const Vector<MpFloat,DIM> &v1,const Vector<MpFloat,DIM> &v2);
template bool operator<= <MpFloat,DIM> (const Vector<MpFloat,DIM> &v1,const Vector<MpFloat,DIM> &v2);
template bool operator>= <MpFloat,DIM> (const Vector<MpFloat,DIM> &v1,const Vector<MpFloat,DIM> &v2);
template std::ostream &operator<< <MpFloat,DIM> (std::ostream &out, const Vector<MpFloat,DIM> &v);
template std::istream &operator>> <MpFloat,DIM>(std::istream &inp, Vector<MpFloat,DIM> &v);

template void subtractObjects<>(const Vector<MpFloat,DIM>& v1,const Vector<MpFloat,DIM>& v2, Vector<MpFloat,DIM>& result);
template void addObjects<>(const Vector<MpFloat,DIM>& v1,const Vector<MpFloat,DIM>& v2, Vector<MpFloat,DIM>& result);

}}  // end of namespace capd::vectalg

#endif // __HAVE_MPFR__
