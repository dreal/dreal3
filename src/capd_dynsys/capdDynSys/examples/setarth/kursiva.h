/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file kursiva.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_TESTS_SETARTH_KURSIVA_H_ 
#define _CAPD_TESTS_SETARTH_KURSIVA_H_ 
#include "capd/capdlib.h"
using namespace capd;

class KurSiva : public IOde{
public:
  KurSiva(const Interval& the_l, const Interval& the_d);
  IVector f(const IVector &iv) const;
  IMatrix df(const IVector &iv) const;
  IMatrix d2f(int i,const IVector &iv) const;
  void set_l(const Interval& the_l);
protected:
  Interval l,d;
};


//inline definitions

inline KurSiva::KurSiva(const Interval& the_l, const Interval& the_d)
   : l(the_l),d(the_d)
{}

inline void KurSiva::set_l(const Interval& the_l)
{
   l = the_l;
}

#endif // _CAPD_TESTS_SETARTH_KURSIVA_H_ 

/// @}
