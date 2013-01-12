/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file GraphicsHSet3D.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 


#include "capd/covrel/GraphicsHSet3D.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.hpp"

using namespace capd::matrixAlgorithms;

namespace capd{
namespace covrel{

typedef HSet3D::FloatVector FloatVector;
typedef HSet3D::IntervalVector IntervalVector;
typedef HSet3D::FloatMatrix FloatMatrix;
typedef HSet3D::IntervalMatrix IntervalMatrix;

void GraphicsHSet3D::show(Frame &f, int d1, int d2) const
{
  FloatVector A = M.column(d1) + M.column(d2);
  FloatVector B = -A;
  A=gauss(M,A);
  B=gauss(M,B);
  f.box(A[d1],A[d2],B[d1],B[d2]);
}

void GraphicsHSet3D::show(Frame &f, int d1, int d2, const IntervalVector &iv, int color) const
{
  FloatVector A = M.column(d1) + M.column(d2);
  FloatVector B = -A;
  A=gauss(M,A);
  B=gauss(M,B);
  f.box(A[d1],A[d2],B[d1],B[d2]);

  IntervalVector v = gauss(IM,iv - Icenter);
  IntervalVector Left = leftVector(v);
  IntervalVector Right = rightVector(v);
  FloatVector L=FloatVector(Left[0].leftBound(),Left[1].leftBound(),Left[2].leftBound());
  FloatVector R=FloatVector(Right[0].leftBound(),Right[1].leftBound(),Right[2].leftBound());

  f.boxFill(L[d1],L[d2],R[d1],R[d2],color);
  f.box(L[d1],L[d2],R[d1],R[d2]);
}

void GraphicsHSet3D::show(Coord3D &f) const
{
  f.jump(RA[0],RA[1],RA[2]);
  f.lineTo(RB[0],RB[1],RB[2]);
  f.lineTo(RC[0],RC[1],RC[2]);
  f.lineTo(RD[0],RD[1],RD[2]);
  f.lineTo(RA[0],RA[1],RA[2]);

  f.jump(LA[0],LA[1],LA[2]);
  f.lineTo(LB[0],LB[1],LB[2]);
  f.lineTo(LC[0],LC[1],LC[2]);
  f.lineTo(LD[0],LD[1],LD[2]);
  f.lineTo(LA[0],LA[1],LA[2]);

  f.line(RA[0],RA[1],RA[2],LA[0],LA[1],LA[2]);
  f.line(RB[0],RB[1],RB[2],LB[0],LB[1],LB[2]);
  f.line(RC[0],RC[1],RC[2],LC[0],LC[1],LC[2]);
  f.line(RD[0],RD[1],RD[2],LD[0],LD[1],LD[2]);
}

void GraphicsHSet3D::show(Coord3D &f, const IntervalVector &v, int color) const
{
  show(f);
  f.box(v[0].leftBound(),v[1].leftBound(),v[2].leftBound(),v[0].rightBound(),v[1].rightBound(),v[2].rightBound(),color);
}

Coord3D& operator << (Coord3D& F, const GraphicsHSet3D &S)
{
  S.show(F);
  return F;
}

}} // namespace capd:covrel

/// @}
