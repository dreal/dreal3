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
	Lorenz(const DInterval& the_s, const DInterval& the_R, const DInterval& the_q);
	IVector f(const IVector &iv) const;
	IMatrix df(const IVector &iv) const;
	IMatrix d2f(int i,const IVector &iv) const;
	DInterval getR(void) const;
protected:
	DInterval s,R,q;
};

class LorenzEuler : public IDynSys{
public:
	LorenzEuler(Lorenz &the_lorenz, const DInterval& the_h);
	IVector Phi(const IVector &iv) const;
	IMatrix JacPhi(const IVector &iv) const;
	IVector Remainder(const IVector &iv) const;
protected:
	Lorenz &lorenz;
	DInterval h;
};


//inline definitions

inline Lorenz::Lorenz(const DInterval& the_s, const DInterval& the_R, const DInterval& the_q)
	: s(the_s),R(the_R),q(the_q)
{}

inline LorenzEuler::LorenzEuler(Lorenz &the_lorenz, const DInterval& the_h)
	: lorenz(the_lorenz),h(the_h)
{}

inline IVector LorenzEuler::Remainder(const IVector &iv) const
{
	IVector result;
	result.clear();
	return result;
}

inline DInterval Lorenz::getR(void) const
{
	return R;
}

#endif // _CAPD_TESTS_SETARTH_LORENZ_H_ 

/// @}
