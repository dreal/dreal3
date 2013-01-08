/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file lorenz4.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "lorenz4.h"

#if (DIM == 4)

IVector Lorenz4::f(const IVector &x) const
{
	IVector result;
	result[0] = s*(x[1]-x[0]);
	result[1] = (R-x[2])*x[0]-x[1];
	result[2] = x[0]*x[1]-q*x[2];
	result[3] = -L*x[3];
	return result;
}

IMatrix Lorenz4::df(const IVector &x) const
{
	IMatrix result;
	result[0][0] = -s;
	result[0][1] = s;
	result[0][2] = Interval(0.);
	result[0][3] = Interval(0.);
	result[1][0] = R-x[2];
	result[1][1] = Interval(-1.);
	result[1][2] = -x[0];
	result[1][3] = Interval(0.);
	result[2][0] = x[1];
	result[2][1] = x[0];
	result[2][2] = -q;
	result[2][3] = Interval(0.);
	result[3][0] = Interval(0.);
	result[3][1] = Interval(0.);
	result[3][2] = Interval(0.);
	result[3][3] = -L;
	return result;
}

IMatrix Lorenz4::d2f(int i, const IVector &x) const
{
	IMatrix result;
	if(i==1){
		result[0][2] = Interval(-1.);
		result[2][0] = Interval(-1.);
	}
	if(i==2){
		result[0][1] = Interval(1.);
		result[1][0] = Interval(1.);
	}
	return result;
}

#endif

/// @}
