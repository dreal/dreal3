/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file HSet3D.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <stdexcept>
#include "capd/covrel/HSet3D.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

using namespace capd::matrixAlgorithms;

namespace capd{
namespace covrel{

typedef HSet3D::FloatVector FloatVector;
typedef HSet3D::IntervalVector IntervalVector;
typedef HSet3D::IntervalMatrix IntervalMatrix;

HSet3D::HSet3D(const FloatVector &Center, const FloatVector &U, const FloatVector &S1, const FloatVector &S2)
  :  center(Center),
    u(U),
    s1(S1),
    s2(S2),
    Icenter(center),
    Iu(u),
    Is1(s1),
    Is2(s2)
{
// first we check, if vectors u, s1, s2 are lineary independent
  double det = u[0]*s1[1]*s2[2] + s1[0]*s2[1]*u[2] + s2[0]*u[1]*s1[2]
              - s2[0]*s1[1]*u[2] - u[0]*s2[1]*s1[2] - u[1]*s1[0]*s2[2];

  if(!det)
  {
    throw std::runtime_error("HSet3D: Cannot create object, vectors linearly dependent");
  }

  RA = center + u + s1 + s2;
  RB = center + u + s1 - s2;
  RC = center + u - s1 - s2;
  RD = center + u - s1 + s2;

  LA = center - u + s1 + s2;
  LB = center - u + s1 - s2;
  LC = center - u - s1 - s2;
  LD = center - u - s1 + s2;

  IRA = IntervalVector(RA);
  IRB = IntervalVector(RB);
  IRC = IntervalVector(RC);
  IRD = IntervalVector(RD);

  ILA = IntervalVector(LA);
  ILB = IntervalVector(LB);
  ILC = IntervalVector(LC);
  ILD = IntervalVector(LD);

  M.column(0) = u;
  M.column(1) = s1;
  M.column(2) = s2;

  IM = IntervalMatrix(M);
} // end of constructor

// -----------------------------------------------------------------------


HSet3D::HSet3D(
    const IntervalVector &Center,
    const IntervalVector &U,
    const IntervalVector &S1,
    const IntervalVector &S2
  ) : Icenter(Center), Iu(U), Is1(S1), Is2(S2)
{
// first we check, if vectors u, s1, s2 are lineary independent
  interval det = Iu[0]*Is1[1]*Is2[2] + Is1[0]*Is2[1]*Iu[2] + Is2[0]*Iu[1]*Is1[2]
               - Is2[0]*Is1[1]*Iu[2] - Iu[0]*Is2[1]*Is1[2] - Iu[1]*Is1[0]*Is2[2];

  if(det.contains(0.0))
  {
    throw std::runtime_error("HSet3D: Cannot create object, vectors linearly dependent");
  }

  IRA = Icenter + Iu + Is1 + Is2;
  IRB = Icenter + Iu + Is1 - Is2;
  IRC = Icenter + Iu - Is1 - Is2;
  IRD = Icenter + Iu - Is1 + Is2;

  ILA = Icenter - Iu + Is1 + Is2;
  ILB = Icenter - Iu + Is1 - Is2;
  ILC = Icenter - Iu - Is1 - Is2;
  ILD = Icenter - Iu - Is1 + Is2;

  IntervalVector v = midVector(Icenter);
  center = FloatVector(v[0].leftBound(),v[1].leftBound(),v[2].leftBound());
  v = midVector(Iu);
  u = FloatVector(v[0].leftBound(),v[1].leftBound(),v[2].leftBound());
  v = midVector(Is1);
  s1 = FloatVector(v[0].leftBound(),v[1].leftBound(),v[2].leftBound());
  v = midVector(Is2);
  s2 = FloatVector(v[0].leftBound(),v[1].leftBound(),v[2].leftBound());

  RA = center + u + s1 + s2;
  RB = center + u + s1 - s2;
  RC = center + u - s1 - s2;
  RD = center + u - s1 + s2;

  LA = center - u + s1 + s2;
  LB = center - u + s1 - s2;
  LC = center - u - s1 - s2;
  LD = center - u - s1 + s2;

  M.column(0) = u;
  M.column(1) = s1;
  M.column(2) = s2;
   
  IM.column(0) = Iu;
  IM.column(1) = Is1;
  IM.column(2) = Is2;
} // end of constructor


// -----------------------------------------------------------------

bool HSet3D::onLeft(const FloatVector &point) const
{
  FloatVector im = gauss(M,point-center);
  return (im[0]<-1.);
}

bool HSet3D::onRight(const FloatVector &point) const
{
  FloatVector im = gauss(M,point-center);
  return (im[0]>1.);
}

bool HSet3D::mapaway(const FloatVector &point) const
{
  FloatVector im = gauss(M,point-center);
  return (im[0]>1. || im[0]<-1.);
}

bool HSet3D::inside(const FloatVector &point) const
{
  FloatVector im = abs(gauss(M,point-center));
  return (im[0]<1. && im[1] < 1. && im[2]<1.);
}

bool HSet3D::outside(const FloatVector &point) const
{
  FloatVector im = gauss(M,point-center);
  return (im[0]>1. || im[0] <-1. || im[1]>1. || im[1]<-1. || im[2]>1. || im[2]<-1.);
}

bool HSet3D::across(const FloatVector &point) const
{
  FloatVector im = gauss(M,point-center);
  if(im[0] < -1. || im[0] > 1.)
    return true;

  return (im[1] < 1. && im[1]>-1. && im[2] < 1. && im[2]>-1.);
}

// ---------------  interval version -------------------------

bool HSet3D::onLeft(const IntervalVector &point) const
{
  IntervalVector im = gauss(IM,point-Icenter);
  return (im[0]<-1.);
}

bool HSet3D::onRight(const IntervalVector &point) const
{
  IntervalVector im = gauss(IM,point-Icenter);
  return (im[0]>1.);
}

bool HSet3D::mapaway(const IntervalVector &point) const
{
  IntervalVector im = gauss(IM,point-Icenter);
  return (im[0]>1. || im[0]<-1.);
}

bool HSet3D::inside(const IntervalVector &point) const
{
  IntervalVector im = gauss(IM,point-Icenter);
  return (im[0]<1. && im[0]>-1. && im[1]<1. && im[1]>-1. && im[2]<1. && im[2]>-1.);
}

bool HSet3D::outside(const IntervalVector &point) const
{
  IntervalVector im = gauss(IM,point-Icenter);
  return (im[0]>1. || im[0]<-1. || im[1]>1. || im[1]<-1. || im[2]>1. || im[2]<-1.);
}

bool HSet3D::across(const IntervalVector &point) const
{
  IntervalVector im = gauss(IM,point-Icenter);
  if(im[0]<-1. || im[0]>1.)
    return true;
  return (im[1] < 1.&& im[1]>-1. && im[2] < 1. && im[2]>-1.);
}

bool InSide(const HSet3D &S, const IntervalVector &IV)
{
  return S.inside(IV);
}
bool OutSide(const HSet3D &S, const IntervalVector &IV)
{
  return S.outside(IV);
}
bool Across(const HSet3D &S, const IntervalVector &IV)
{
  return S.across(IV);
}
bool MapAway(const HSet3D &S, const IntervalVector &IV)
{
  return S.mapaway(IV);
}
bool LeftSide(const HSet3D &S, const IntervalVector &IV)
{
  return S.onLeft(IV);
}
bool RightSide(const HSet3D &S, const IntervalVector &IV)
{
  return S.onRight(IV);
}

// ----------------------------------------------------

bool InSide(const HSet3D &S, const FloatVector &IV)
{
  return S.inside(IV);
}
bool OutSide(const HSet3D &S, const FloatVector &IV)
{
  return S.outside(IV);
}
bool Across(const HSet3D &S, const FloatVector &IV)
{
  return S.across(IV);
}
bool MapAway(const HSet3D &S, const FloatVector &IV)
{
  return S.mapaway(IV);
}
bool LeftSide(const HSet3D &S, const FloatVector &IV)
{
  return S.onLeft(IV);
}
bool RightSide(const HSet3D &S, const FloatVector &IV)
{
  return S.onRight(IV);
}

}} // namespace capd::covrel

/// @}
