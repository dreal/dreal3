/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file lorenz.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "lorenz.h"

#if (DIM == 3)

IVector Lorenz::f(const IVector &x) const
{
  IVector result;
  result[0] = s*(x[1]-x[0]);
  result[1] = (R-x[2])*x[0]-x[1];
  result[2] = x[0]*x[1]-q*x[2];
  return result;
}

IMatrix Lorenz::df(const IVector &x) const
{
  IMatrix result;
  result[0][0] = -s;
  result[0][1] = s;
  result[0][2] = DInterval(0.);
  result[1][0] = R-x[2];
  result[1][1] = DInterval(-1.);
  result[1][2] = -x[0];
  result[2][0] = x[1];
  result[2][1] = x[0];
  result[2][2] = -q;
  return result;
}

IMatrix Lorenz::d2f(int i, const IVector &x) const
{
  IMatrix result;
  if(i==1){
    result[0][2] = DInterval(-1.);
    result[2][0] = DInterval(-1.);
  }
  if(i==2){
    result[0][1] = DInterval(1.);
    result[1][0] = DInterval(1.);
  }
  return result;
}

IVector LorenzEuler::Phi(const IVector &x) const
{
  return x+h*lorenz.f(x);
}

IMatrix LorenzEuler::JacPhi(const IVector &x) const
{
  return IMatrix::Identity(3)+h*lorenz.df(x);
}

#endif

/// @}
