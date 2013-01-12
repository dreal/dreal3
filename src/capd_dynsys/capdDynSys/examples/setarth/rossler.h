/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file rossler.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_TESTS_SETARTH_ROSSLER_H_ 
#define _CAPD_TESTS_SETARTH_ROSSLER_H_ 

#include "capd/capdlib.h"
using namespace capd;

class Rossler : public IOde{
public:
	Rossler(const Interval& the_a, const Interval &the_b);
	IVector f(const IVector &iv) const;
	IMatrix df(const IVector &iv) const;
	IMatrix d2f(int i,const IVector &iv) const;
      
//    protected:    
	Interval a,b;
};

class RosslerEuler : public IDynSys{
public:
	RosslerEuler(Rossler &the_rossler, Interval the_h);
	IVector Phi(const IVector &iv) const;
	IMatrix JacPhi(const IVector &iv) const;
	IVector Remainder(const IVector &iv) const;
protected:
	Rossler &rossler;
	Interval h;
};


//inline definitions

inline Rossler::Rossler(const Interval& the_a, const Interval& the_b)
	: a(the_a),b(the_b)
{}

inline RosslerEuler::RosslerEuler(Rossler &the_rossler, Interval the_h)
	: rossler(the_rossler),h(the_h)
{}

inline IVector RosslerEuler::Remainder(const IVector &iv) const
{
	IVector result;
	result.clear();
	return result;
}

#endif // _CAPD_TESTS_SETARTH_ROSSLER_H_ 

/// @}
