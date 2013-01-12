/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file lorenz.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_TESTS_SETARTH_LORENZ_H_ 
#define _CAPD_TESTS_SETARTH_LORENZ_H_ 

#include "capd/capdlib.h"
using namespace capd;

class Lorenz : public IOde{
public:
	Lorenz(const Interval& the_s, const Interval& the_R, const Interval& the_q);
	IVector f(const IVector &iv) const;
	IMatrix df(const IVector &iv) const;
	IMatrix d2f(int i,const IVector &iv) const;
	Interval getR(void) const;
protected:
	Interval s,R,q;
};

class LorenzEuler : public IDynSys{
public:
	LorenzEuler(Lorenz &the_lorenz, const Interval& the_h);
	IVector Phi(const IVector &iv) const;
	IMatrix JacPhi(const IVector &iv) const;
	IVector Remainder(const IVector &iv) const;
protected:
	Lorenz &lorenz;
	Interval h;
};


//inline definitions

inline Lorenz::Lorenz(const Interval& the_s, const Interval& the_R, const Interval& the_q)
	: s(the_s),R(the_R),q(the_q)
{}

inline LorenzEuler::LorenzEuler(Lorenz &the_lorenz, const Interval& the_h)
	: lorenz(the_lorenz),h(the_h)
{}

inline IVector LorenzEuler::Remainder(const IVector &iv) const
{
	IVector result;
	result.clear();
	return result;
}

inline Interval Lorenz::getR(void) const
{
	return R;
}

#endif // _CAPD_TESTS_SETARTH_LORENZ_H_ 

/// @}
