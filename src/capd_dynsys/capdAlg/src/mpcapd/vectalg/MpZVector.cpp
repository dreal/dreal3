
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


template class Vector<MpInt,DIM>;

template Vector<MpInt,DIM> abs<MpInt,DIM> (const Vector<MpInt,DIM> &v);
template Vector<MpInt,DIM> operator- <MpInt,DIM> (const Vector<MpInt,DIM> &v);
template Vector<MpInt,DIM> operator+ <MpInt,DIM> (const Vector<MpInt,DIM> &v1,const Vector<MpInt,DIM> &v2);
template Vector<MpInt,DIM> operator- <MpInt,DIM> (const Vector<MpInt,DIM> &v1,const Vector<MpInt,DIM> &v2);
template MpInt operator* <MpInt,DIM> (const Vector<MpInt,DIM> &v1,const Vector<MpInt,DIM> &v2);

template Vector<MpInt,DIM> operator* <MpInt,MpInt,DIM> (const Vector<MpInt,DIM> &v,const MpInt &s);
template Vector<MpInt,DIM> operator* <MpInt,MpInt,DIM> (const MpInt &s,const Vector<MpInt,DIM> &v);
template Vector<MpInt,DIM> operator/ <MpInt,MpInt,DIM> (const Vector<MpInt,DIM> &v, const MpInt &s);

template Vector<MpInt,DIM> operator* <MpInt,long,DIM>(const Vector<MpInt,DIM> &v,const long &s);
template Vector<MpInt,DIM> operator* <MpInt,long,DIM>(const long &s,const Vector<MpInt,DIM> &v);
template Vector<MpInt,DIM> operator/ <MpInt,long,DIM>(const Vector<MpInt,DIM> &v, const long &s);

template Vector<MpInt,DIM> operator* <MpInt,int,DIM>(const Vector<MpInt,DIM> &v,const int &s);
template Vector<MpInt,DIM> operator* <MpInt,int,DIM>(const int &s,const Vector<MpInt,DIM> &v);
template Vector<MpInt,DIM> operator/ <MpInt,int,DIM>(const Vector<MpInt,DIM> &v, const int &s);

template Vector<MpInt,DIM> operator+ <MpInt,DIM> (const Vector<MpInt,DIM> &v,const MpInt &s);
template Vector<MpInt,DIM> operator- <MpInt,DIM> (const Vector<MpInt,DIM> &v,const MpInt &s);
template bool operator < <MpInt,DIM> (const Vector<MpInt,DIM> &v1,const Vector<MpInt,DIM> &v2);
template bool operator > <MpInt,DIM> (const Vector<MpInt,DIM> &v1,const Vector<MpInt,DIM> &v2);
template bool operator<= <MpInt,DIM> (const Vector<MpInt,DIM> &v1,const Vector<MpInt,DIM> &v2);
template bool operator>= <MpInt,DIM> (const Vector<MpInt,DIM> &v1,const Vector<MpInt,DIM> &v2);
template std::ostream &operator<< <MpInt,DIM> (std::ostream &out, const Vector<MpInt,DIM> &v);
template std::istream &operator>> <MpInt,DIM>(std::istream &inp, Vector<MpInt,DIM> &v);

template void subtractObjects<>(const Vector<MpInt,DIM>& v1,const Vector<MpInt,DIM>& v2, Vector<MpInt,DIM>& result);
template void addObjects<>(const Vector<MpInt,DIM>& v1,const Vector<MpInt,DIM>& v2, Vector<MpInt,DIM>& result);

}}  // end of namespace capd::vectalg

#endif // __HAVE_MPFR__
