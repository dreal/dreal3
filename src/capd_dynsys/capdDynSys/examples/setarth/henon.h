/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file henon.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_TESTS_SETARTH_HENON_H_ 
#define _CAPD_TESTS_SETARTH_HENON_H_ 

#include "capd/capdlib.h"
using namespace capd;

class Henon : public IDynSys{
public:
	Henon(const Interval& the_a, const Interval& the_b);
	IVector Phi(const IVector &iv) const;
	IMatrix JacPhi(const IVector &iv) const;
	IVector Remainder(const IVector &iv) const;
protected:
	Interval a,b;
}; 

inline Henon::Henon(const Interval& the_a, const Interval& the_b)
{
	a=the_a;b=the_b;
}     

inline IVector Henon::Remainder(const IVector &iv) const
{
	IVector result;
	result.clear();
	return result;
}
#endif // _CAPD_TESTS_SETARTH_HENON_H_ 

/// @}
