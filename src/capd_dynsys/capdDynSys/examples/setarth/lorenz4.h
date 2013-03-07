/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file lorenz4.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_TESTS_SETARTH_LORENZ4_H_ 
#define _CAPD_TESTS_SETARTH_LORENZ4_H_ 
#include "capd/capdlib.h"
using namespace capd;

class Lorenz4 : public IOde{
public:
	Lorenz4(const DInterval& the_s, const DInterval& the_R, const DInterval& the_q, const DInterval& the_L);
	IVector f(const IVector &iv) const;
	IMatrix df(const IVector &iv) const;
	IMatrix d2f(int i, const IVector &iv) const;
	DInterval getR(void) const;
protected:
	DInterval s,R,q,L;
};



//inline definitions

inline Lorenz4::Lorenz4(const DInterval& the_s, const DInterval& the_R,
				const DInterval& the_q, const DInterval& the_L)
	: s(the_s),R(the_R),q(the_q),L(the_L)
{}

inline DInterval Lorenz4::getR(void) const
{
	return R;
}

#endif // _CAPD_TESTS_SETARTH_LORENZ4_H_ 

/// @}
