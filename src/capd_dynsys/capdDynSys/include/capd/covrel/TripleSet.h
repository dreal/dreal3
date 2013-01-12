/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file TripleSet.h
///
/// @author Jaroslaw Dulak, Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#ifndef _CAPD_COVREL_TRIPLESET_H_
#define _CAPD_COVREL_TRIPLESET_H_

#include <vector>
#include "capd/intervals/DoubleInterval.h"
#include "capd/vectalg/Vector.hpp"
#include "capd/vectalg/Matrix.hpp"
#include "capd/covrel/HSet.h"

namespace capd{
namespace covrel{
/**
   TripleSet - a planar h-set with one unstable direction
   Authors: Implementation of derived classes and functions: Jaroslaw Dulak and Daniel Wilczak.
*/
class TripleSet : public HSet<capd::vectalg::Vector<double,2>, capd::vectalg::Vector<interval,2> >
{
public:
  typedef capd::vectalg::Vector<double,2>     FloatVector;
  typedef capd::vectalg::Vector<interval,2>   IntervalVector;
  typedef IntervalVector::ScalarType Interval;

  TripleSet(const FloatVector& a_center, const FloatVector& a_stable, const FloatVector& a_unstable);
  TripleSet(const IntervalVector& a_center, const IntervalVector& a_stable, const IntervalVector& a_unstable);
  TripleSet() : max_recursion(256){}
  ~TripleSet(){}

  bool outside (const FloatVector &point) const;
  bool inside  (const FloatVector &point) const;
  bool across  (const FloatVector &point) const;
  bool mapaway (const FloatVector &point) const;
  bool onLeft  (const FloatVector &point) const;
  bool onRight (const FloatVector &point) const;

  bool outside (const IntervalVector &point) const;
  bool inside  (const IntervalVector &point) const;
  bool across  (const IntervalVector &point) const;
  bool mapaway (const IntervalVector &point) const;
  bool onLeft  (const IntervalVector &point) const;
  bool onRight (const IntervalVector &point) const;

  /**
   * in the G it returns uniform grid of the left edge
   *
   * @param grid    number of pieces in the grid
   * @param d1, d2  if hset is embeded in higher dimension
   *                than we put first coordinate in d1, second in d2 the rest sets to 0.
   */
  template<typename IMatrix>
  GridSet<IMatrix>& gridLeftEdge(GridSet<IMatrix>& G, int grid, int d1=0, int d2=1) const;
  template<typename IMatrix>
  GridSet<IMatrix>& gridRightEdge(GridSet<IMatrix>& G, int grid, int d1=0, int d2=1) const;
  template<typename IMatrix>
  GridSet<IMatrix>& gridBottomEdge(GridSet<IMatrix>& G, int grid, int d1=0, int d2=1) const;
  template<typename IMatrix>
  GridSet<IMatrix>& gridTopEdge(GridSet<IMatrix>& G, int grid, int d1=0, int d2=1) const;
  template<typename IMatrix>
  GridSet<IMatrix>& gridSet(GridSet<IMatrix>& G, int grid1, int grid2, int d1=0, int d2=1) const;

  //  the support given by: Icenter + [-1,1]*Iunstable + [-1,1]*Istable
  FloatVector center, stable, unstable;
  IntervalVector Icenter, Istable, Iunstable;

  FloatVector A, B, C, D;
  IntervalVector IA, IB, IC, ID;
  // vectors IA,IB,IC,ID - corners of the support
  //          A,B,C,D - corners as double - for double (nonrigorous) functions
  // It is essential for other methods within this class that:
  //
  // the exit set - N^- = AD  \cup BC
  // and if we order corners as follows (A,B,C,D,A,B,..)
  // all possible triples are positively oriented , this means
  // that if we consider for example (A,B,C) then the following
  // path A- > B -> C -> A is orientated counterclockwise
  // egde (DA) - is then a 'left' egde - and the condition
  //        for a point to be on the left side is - orientation(D,A,point)=-1
  // BC - is the 'right' edge - the condition on being on the right side
  //          is orientation (C,B,point)=1

  int max_recursion; //used in the function across

private:
  // both functions (orientation, Iorientation) return an orientation
  // of a triple (v1,v2,v3) 1- anticlockwise, -1 - clockwise, 0 - collinear
  int orientation(const FloatVector &v1,const FloatVector &v2,const FloatVector &v3) const;
  int Iorientation(const IntervalVector &v1,const IntervalVector &v2,const IntervalVector& v3) const;


  // the function checks if the segment (supp_1,supp_2) intersects the segment (vect_1,vect_2)
  // in an interior point for both segments
  // if this is the case then true is returned
  bool checkIntersection(const IntervalVector &supp_1,
                        const IntervalVector &supp_2,
                        const IntervalVector &vect1,
                        const IntervalVector &vect2) const;
}; //end of class TripleSet


// sometime we need a pointer to a function verifying covering relations for
// triple sets:
// bool (*f)(TripleSet &, IntervalVector &);
// the functions are:

template<typename IVector>
bool InSide(const TripleSet &S, const IVector &IV, int d1, int d2)
{
  typename TripleSet::IntervalVector v;
  v[0] = IV[d1];
  v[1] = IV[d2];
  return S.inside(v);
}

inline bool InSide(const TripleSet& S, const TripleSet::IntervalVector& v)
{
  return S.inside(v);
}

template<typename IVector>
bool OutSide(const TripleSet &S, const IVector &IV, int d1, int d2)
{
  TripleSet::IntervalVector v;
  v[0] = IV[d1];
  v[1] = IV[d2];
  return S.outside(v);
}

inline bool OutSide(const TripleSet& S, const TripleSet::IntervalVector& v)
{
  return S.outside(v);
}

template<typename IVector>
bool Across(const TripleSet &S, const IVector &IV, int d1, int d2)
{
  TripleSet::IntervalVector v;
  v[0] = IV[d1];
  v[1] = IV[d2];
  return S.across(v);
}

inline bool Across(const TripleSet& S, const TripleSet::IntervalVector& v)
{
  return S.across(v);
}

template<typename IVector>
bool MapAway(const TripleSet &S, const IVector &IV, int d1, int d2)
{
  TripleSet::IntervalVector v;
  v[0] = IV[d1];
  v[1] = IV[d2];
  return S.mapaway(v);
}

inline bool MapAway(const TripleSet& S, const TripleSet::IntervalVector& v)
{
  return S.mapaway(v);
}

template<typename IVector>
bool LeftSide(const TripleSet &S, const IVector &IV, int d1, int d2)
{
  TripleSet::IntervalVector v;
  v[0] = IV[d1];
  v[1] = IV[d2];
  return S.onLeft(v);
}

inline bool LeftSide(const TripleSet& S, const TripleSet::IntervalVector& v)
{
  return S.onLeft(v);
}

template<typename IVector>
bool RightSide(const TripleSet &S, const IVector &IV, int d1, int d2)
{
  TripleSet::IntervalVector v;
  v[0] = IV[d1];
  v[1] = IV[d2];
  return S.onRight(v);
}

inline bool RightSide(const TripleSet& S, const TripleSet::IntervalVector& v)
{
  return S.onRight(v);
}
// -------------------------------------------------------------

template<typename IMatrix>
GridSet<IMatrix>& TripleSet::gridLeftEdge(GridSet<IMatrix>& G, int grid, int d1, int d2) const
{
  G.center.resize(grid);

  G.C.setToIdentity();
  G.C[d1][d1] = Iunstable[0];
  G.C[d2][d1] = Iunstable[1];
  G.C[d1][d2] = Istable[0];
  G.C[d2][d2] = Istable[1];

  IntervalVector s = 2*Istable/grid;
  IntervalVector corner = Icenter - Iunstable - Istable;

  G.r[d1] = 0;
  G.r[d2] = Interval(-1,1)/grid;

  typename GridSet<IMatrix>::VectorType step;
  step[d1] = s[0];
  step[d2] = s[1];

  typename GridSet<IMatrix>::VectorType c;
  c[d1] = corner[0];
  c[d2] = corner[1];

  for(int i=0;i<grid;i++)
  {
    G.center[i] = c + (i+0.5)*step;
  }
  return G;
}

// -------------------------------------------------------------

template<typename IMatrix>
GridSet<IMatrix>& TripleSet::gridRightEdge(GridSet<IMatrix>& G, int grid, int d1, int d2) const
{
  G.center.resize(grid);

  G.C.setToIdentity();
  G.C[d1][d1] = Iunstable[0];
  G.C[d2][d1] = Iunstable[1];
  G.C[d1][d2] = Istable[0];
  G.C[d2][d2] = Istable[1];

  IntervalVector s = 2*Istable/grid;
  IntervalVector corner = Icenter + Iunstable - Istable;

  G.r[d1] = 0;
  G.r[d2] = Interval(-1,1)/grid;

  typename GridSet<IMatrix>::VectorType step;
  step[d1] = s[0];
  step[d2] = s[1];

  typename GridSet<IMatrix>::VectorType c;
  c[d1] = corner[0];
  c[d2] = corner[1];

  for(int i=0;i<grid;i++)
  {
    G.center[i] = c + (i+0.5)*step;
  }
  return G;
}

// -------------------------------------------------------------

template<typename IMatrix>
GridSet<IMatrix>& TripleSet::gridBottomEdge(GridSet<IMatrix>& G, int grid, int d1, int d2) const
{
  G.center.resize(grid);

  G.C.setToIdentity();
  G.C[d1][d1] = Iunstable[0];
  G.C[d2][d1] = Iunstable[1];
  G.C[d1][d2] = Istable[0];
  G.C[d2][d2] = Istable[1];

  IntervalVector s = 2*Iunstable/grid;
  IntervalVector corner = Icenter - Iunstable - Istable;

  G.r[d1] = Interval(-1,1)/grid;
  G.r[d2] = 0;

  typename GridSet<IMatrix>::VectorType step;
  step[d1] = s[0];
  step[d2] = s[1];

  typename GridSet<IMatrix>::VectorType c;
  c[d1] = corner[0];
  c[d2] = corner[1];

  for(int i=0;i<grid;i++)
  {
    G.center[i] = c + (i+0.5)*step;
  }
  return G;
}


// -------------------------------------------------------------

template<typename IMatrix>
GridSet<IMatrix>& TripleSet::gridTopEdge(GridSet<IMatrix>& G, int grid, int d1, int d2) const
{
  G.center.resize(grid);

  G.C.setToIdentity();
  G.C[d1][d1] = Iunstable[0];
  G.C[d2][d1] = Iunstable[1];
  G.C[d1][d2] = Istable[0];
  G.C[d2][d2] = Istable[1];

  IntervalVector s = 2*Iunstable/grid;
  IntervalVector corner = Icenter - Iunstable + Istable;

  G.r[d1] = Interval(-1,1)/grid;
  G.r[d2] = 0;

  typename GridSet<IMatrix>::VectorType step;
  step[d1] = s[0];
  step[d2] = s[1];

  typename GridSet<IMatrix>::VectorType c;
  c[d1] = corner[0];
  c[d2] = corner[1];

  for(int i=0;i<grid;i++)
  {
    G.center[i] = c + (i+0.5)*step;
  }
  return G;
}


// -------------------------------------------------------------

template<typename IMatrix>
GridSet<IMatrix>& TripleSet::gridSet(GridSet<IMatrix>& G, int grid1, int grid2, int d1, int d2) const
{
  G.center.resize(grid1*grid2);

  G.C.setToIdentity();
  G.C[d1][d1] = Iunstable[0];
  G.C[d2][d1] = Iunstable[1];
  G.C[d1][d2] = Istable[0];
  G.C[d2][d2] = Istable[1];

  IntervalVector s1 = 2*Iunstable/grid1;
  IntervalVector s2 = 2*Istable/grid2;
  IntervalVector corner = Icenter - Iunstable - Istable;

  G.r[d1] = Interval(-1,1)/grid1;
  G.r[d2] = Interval(-1,1)/grid2;

  typename GridSet<IMatrix>::VectorType step1, step2;
  step1[d1] = s1[0];
  step1[d2] = s1[1];
  step2[d1] = s2[0];
  step2[d2] = s2[1];

  typename GridSet<IMatrix>::VectorType c;
  c[d1] = corner[0];
  c[d2] = corner[1];

  for(int i=0;i<grid1;i++)
    for(int j=0;j<grid2;j++)
      G.center[i*grid2+j] = c + (i+0.5)*step1 + (j+0.5)*step2;

  return G;
}

}} //namespace capd::covrel

#endif // _CAPD_COVREL_TRIPLESET_H_

/// @}
