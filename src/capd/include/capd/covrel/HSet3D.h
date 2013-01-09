/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file HSet3D.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_COVREL_HSET3D_H_ 
#define _CAPD_COVREL_HSET3D_H_ 

#include "capd/interval/DoubleInterval.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/covrel/HSet.h"

namespace capd{
namespace covrel{

/**
The class HSet3D provides a h-set in R^3 with one unstable direction and two stable directions
*/
class HSet3D : public HSet < capd::vectalg::Vector<double,3>, capd::vectalg::Vector<interval,3> >{
public:
  typedef capd::vectalg::Vector<double,3> FloatVector;
  typedef capd::vectalg::Vector<interval,3> IntervalVector;
  typedef capd::vectalg::Matrix<double,3,3> FloatMatrix;
  typedef capd::vectalg::Matrix<interval,3,3> IntervalMatrix;

  HSet3D(){}
  HSet3D(const FloatVector &Center, const FloatVector &U, const FloatVector &S1, const FloatVector &S2);
  HSet3D(const IntervalVector &Center, const IntervalVector &U, const IntervalVector &S1, const IntervalVector &S2);
  ~HSet3D(){}

// double versions
  bool outside(const FloatVector &point) const;
  bool inside (const FloatVector &point) const;
  bool across (const FloatVector &point) const;
  bool mapaway(const FloatVector &point) const;
  bool onLeft (const FloatVector &point) const;
  bool onRight(const FloatVector &point) const;

// interval versions
  bool outside(const IntervalVector &point) const;
  bool inside (const IntervalVector &point) const;
  bool across (const IntervalVector &point) const;
  bool mapaway(const IntervalVector &point) const;
  bool onLeft (const IntervalVector &point) const;
  bool onRight(const IntervalVector &point) const;

  // this procedure creates a grid of a wall of h-set
  // in the following form: G.center[i] + G.C * G.r
  // d1, d2, d3 denote indexes of coordinates if the set is embeded in higher dimension
  // sign = 0 says that the grid should cover both walls pointed by direction 'dir'
  // sign = 1 or -1 says that only one wall will be covered
  template<typename IMatrix>
  GridSet<IMatrix>& gridWall( GridSet<IMatrix>& G,
                              int grid1, int grid2, int dir, int sign=0,
                              int d1=0, int d2=1, int d3=2
                            ) const;


  // this procedure creates a grid of the whole h-set
  // in the following form: G.center[i] + G.C * G.r
  // d1, d2, d3 denote indexes of coordinates if the set is embeded in higher dimension
  template<typename IMatrix>
  GridSet<IMatrix>& gridSet( GridSet<IMatrix> &G,
                             int grid1, int grid2, int grid3,
                             int d1=0, int d2=1, int d3=2
                           ) const;

  FloatVector center;
  FloatVector u;       // one unstable direction
  FloatVector s1,s2;   // two stable directions
  FloatMatrix M;       // a matrix [u,s1,s2]

  IntervalVector Icenter;
  IntervalVector Iu;
  IntervalVector Is1,Is2;
  IntervalMatrix IM;

  FloatVector RA, RB, RC, RD; // right wall of a set
  FloatVector LA, LB, LC, LD; // left wall of a set

  IntervalVector IRA, IRB, IRC, IRD; // right wall of a set
  IntervalVector ILA, ILB, ILC, ILD; // left wall of a set
};

// sometimes we need a pointer to a function which
// verifies covering relations for h-sets
//    int (*f)(HSet3D &, IntevalVector &);
// the functions are:

bool OutSide  (const HSet3D&, const HSet3D::FloatVector &);
bool InSide   (const HSet3D&, const HSet3D::FloatVector &);
bool Across   (const HSet3D&, const HSet3D::FloatVector &);
bool MapAway  (const HSet3D&, const HSet3D::FloatVector &);
bool LeftSide (const HSet3D&, const HSet3D::FloatVector &);
bool RightSide(const HSet3D&, const HSet3D::FloatVector &);

bool OutSide  (const HSet3D&, const HSet3D::IntervalVector &);
bool InSide   (const HSet3D&, const HSet3D::IntervalVector &);
bool Across   (const HSet3D&, const HSet3D::IntervalVector &);
bool MapAway  (const HSet3D&, const HSet3D::IntervalVector &);
bool LeftSide (const HSet3D&, const HSet3D::IntervalVector &);
bool RightSide(const HSet3D&, const HSet3D::IntervalVector &);

template<typename IMatrix>
GridSet<IMatrix>& HSet3D::gridWall( GridSet<IMatrix>& G,
                                    int grid1, int grid2, int dir, int sign,
                                    int d1, int d2, int d3
                                  ) const
{
  typedef typename GridSet<IMatrix>::ScalarType Interval;
  G.C.setToIdentity();
  G.C[d1][d1] = Iu[0];  G.C[d2][d1] = Iu[1];  G.C[d3][d1] = Iu[2];
  G.C[d1][d2] = Is1[0]; G.C[d2][d2] = Is1[1]; G.C[d3][d2] = Is1[2];
  G.C[d1][d3] = Is2[0]; G.C[d2][d3] = Is2[1]; G.C[d3][d3] = Is2[2];

  // if sign=0 both walls will be cover
  if(sign)
    G.center.resize(grid1*grid2);
  else
    G.center.resize(2*grid1*grid2);

  IntervalVector corner1 = Icenter - Iu - Is1 -Is2, corner2;
  IntervalVector v1, v2;
  if(dir==0)
  {
    G.r[d1] = 0;
    G.r[d2] = Interval(-1,1)/grid1;
    G.r[d3] = Interval(-1,1)/grid2;
    corner2 = Icenter + Iu - Is1 -Is2;
    v1 = 2*Is1/grid1;
    v2 = 2*Is2/grid2;
  } else if(dir==1) {
    G.r[d1] = Interval(-1,1)/grid1;
    G.r[d2] = 0;
    G.r[d3] = Interval(-1,1)/grid2;
    corner2 = Icenter - Iu + Is1 -Is2;
    v1 = 2*Iu/grid1;
    v2 = 2*Is2/grid2;
  } else {
    G.r[d1] = Interval(-1,1)/grid1;
    G.r[d2] = Interval(-1,1)/grid2;
    G.r[d3] = 0;
    corner2 = Icenter - Iu - Is1 +Is2;
    v1 = 2*Iu/grid1;
    v2 = 2*Is1/grid2;
  }

  typename GridSet<IMatrix>::VectorType V1,V2;
  V1[d1] = v1[0]; V1[d2] = v1[1]; V1[d3] = v1[2];
  V2[d1] = v2[0]; V2[d2] = v2[1]; V2[d3] = v2[2];

  int i=0,j,k;
  if(!(sign>0))
  {
    typename GridSet<IMatrix>::VectorType c;
    c[d1] = corner1[0];
    c[d2] = corner1[1];
    c[d3] = corner1[2];
    for(j=0;j<grid1;j++)
      for(k=0;k<grid2;k++)
        G.center[i++] = c + (j+0.5)*V1 + (k+0.5)*V2;
  }
  if(!(sign<0))
  {
    typename GridSet<IMatrix>::VectorType c;
    c[d1] = corner2[0];
    c[d2] = corner2[1];
    c[d3] = corner2[2];
    for(j=0;j<grid1;j++)
      for(k=0;k<grid2;k++)
        G.center[i++] = c + (j+0.5)*V1 + (k+0.5)*V2;
  }
  return G;
}

// ----------------------------------------------------

template<typename IMatrix>
GridSet<IMatrix>& HSet3D::gridSet( GridSet<IMatrix>& G,
                                   int grid1, int grid2, int grid3,
                                   int d1, int d2, int d3
                                 ) const
{
  typedef typename GridSet<IMatrix>::ScalarType Interval;
  G.C.setToIdentity();
  G.C[d1][d1] = Iu[0];  G.C[d2][d1] = Iu[1];  G.C[d3][d1] = Iu[2];
  G.C[d1][d2] = Is1[0]; G.C[d2][d2] = Is1[1]; G.C[d3][d2] = Is1[2];
  G.C[d1][d3] = Is2[0]; G.C[d2][d3] = Is2[1]; G.C[d3][d3] = Is2[2];

  G.r[d1] = Interval(-1,1)/grid1;
  G.r[d2] = Interval(-1,1)/grid2;
  G.r[d3] = Interval(-1,1)/grid3;

  IntervalVector v1 = 2*Iu/grid1,
                 v2 = 2*Is1/grid2,
                 v3 = 2*Is2/grid3;

  typename GridSet<IMatrix>::VectorType V1,V2,V3;
  V1[d1] = v1[0]; V1[d2] = v1[1]; V1[d3] = v1[2];
  V2[d1] = v2[0]; V2[d2] = v2[1]; V2[d3] = v2[2];
  V3[d1] = v3[0]; V3[d2] = v3[1]; V3[d3] = v3[2];

  IntervalVector corner = Icenter - Iu - Is1 -Is2;
  typename GridSet<IMatrix>::VectorType c;
  c[d1] = corner[0];
  c[d2] = corner[1];
  c[d3] = corner[2];

  G.center.resize(grid1*grid2*grid3);
  int i,j,k,p=0;
  for(i=0;i<grid1;i++)
    for(j=0;j<grid2;j++)
      for(k=0;k<grid3;k++)
        G.center[p++] = c + (i+0.5)*V1 + (j+0.5)*V2 + (k+0.5)*V3;

  return G;
}

}} // namespace capd::covrel

#endif // _CAPD_COVREL_HSET3D_H_ 

/// @}
