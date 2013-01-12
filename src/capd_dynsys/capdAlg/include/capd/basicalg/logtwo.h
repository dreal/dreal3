/////////////////////////////////////////////////////////////////////////////
/// @file memSize.h
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2006 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#if !defined(_LOGTWO_H_)
#define _LOGTWO_H_

#include <iostream>

/// @addtogroup basicalg
/// @{

template<int N>
struct logtwo{
  static const int value=
    N>=2 ?
    1+logtwo<N/2>::value :
    0;
};
/// @}

template<>
struct logtwo<0>{
  static const int value=0;
};
#endif //_LOGTWO_H_
