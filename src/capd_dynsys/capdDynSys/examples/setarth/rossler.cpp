/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file rossler.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "rossler.h"

#if (DIM == 3)

IVector Rossler::f(const IVector &x) const
{
  IVector result;
  result[0]=-(x[1]+x[2]);
  result[1]=x[0]+b*x[1];
  result[2]=b + x[2]*(x[0]-a);
  return result;
}

IMatrix Rossler::df(const IVector &x) const
{
  IMatrix result;
  result[0][0]=0;
  result[0][1]=-1;
  result[0][2]=-1;
  result[1][0]=1;
  result[1][1]=b;
  result[1][2]=0;
  result[2][0]=x[2];
  result[2][1]=0;
  result[2][2]=x[0]-a;
  return result;
}

IMatrix Rossler::d2f(int i,const IVector &x) const
{
  IMatrix result;
  if(i==2){
    result[0][2]=1;
    result[2][0]=1;
  }
  return result;
}

IVector RosslerEuler::Phi(const IVector &x) const
{
   return x+h*rossler.f(x);
}

IMatrix RosslerEuler::JacPhi(const IVector &x) const
{
  return IMatrix::Identity(3)+h*rossler.df(x);
}

#endif

/// @}
