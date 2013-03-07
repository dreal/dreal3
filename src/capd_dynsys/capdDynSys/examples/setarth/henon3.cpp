/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file henon3.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include "henon3.h"

#if (DIM == 3)

IVector Henon3::Phi(const IVector &iv) const
{
	IVector result;
	result[0] = iv[1] + DInterval(1.) - a*(iv[0]^2);
	result[1] = b*iv[0];
	result[2] = iv[2];
	return result;
}


IMatrix Henon3::JacPhi(const IVector &iv) const
{
	IMatrix result;

/*
    result(1,1)=-2*a*iv(1);
    result(1,2)=1;
    result(2,1)=b;
    result(2,2)=0;
*/
	result[0][0] = DInterval(-2.)*a*iv[0];
	result[0][1] = DInterval(1.);
	result[1][0] = b;
	result[1][1] = DInterval(0.);
	result[2][2] = DInterval(1.);

	return result;
}

#endif

/// @}
