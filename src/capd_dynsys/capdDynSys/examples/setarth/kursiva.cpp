/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file kursiva.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "kursiva.h"

double k_alfa=0.0;
double k_beta=0.0;


IVector KurSiva::f(const IVector &x) const
{
	IVector result;
	result[0] = x[1];
	result[1] = x[2];
	result[2] = -d*d*l*x[1]-x[0]*x[0]/2+d*d*d*d*d*d;
	return result;
}

IMatrix KurSiva::df(const IVector &x) const
{
	IMatrix result;
	result[0][1] = DInterval(1.);
	result[1][2] = DInterval(1.);
	result[2][0] = -x[0];
	result[2][1] = -d*d*l;
	return result;
}

IMatrix KurSiva::d2f(int i,const IVector &x) const
{
	IMatrix result;
	if(i==2){
		result[0][0] = DInterval(-1.);
	}
	return result;
}

/// @}
