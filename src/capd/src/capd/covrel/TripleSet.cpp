/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file TripleSet.cpp
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/covrel/TripleSet.h"
#include <stdexcept>

namespace capd{
namespace covrel{

typedef TripleSet::FloatVector FloatVector;
typedef TripleSet::IntervalVector IntervalVector;

//------------------------ constructors ---------------------------------

TripleSet::TripleSet(const FloatVector& a_center, const FloatVector& a_stable, const FloatVector& a_unstable)
  : center(a_center), stable(a_stable), unstable(a_unstable),
    Icenter(IntervalVector(center)), Istable(IntervalVector(stable)), Iunstable(IntervalVector(unstable)),
    max_recursion(256)
{
  int orien = orientation(center,center + stable,center + unstable);
	if(orien == 0)
  {
    throw std::runtime_error("Cannot create TripleSet - colinear vectors");
  }

	for(int i=0; i<2; ++i)
	{
      // we define corners, so that
      // (A,B,C,D) is oriented counterclockwise
		if(orien == -1)
 		{
			A[i] = center[i] - stable[i] - unstable[i];
			B[i] = center[i] - stable[i] + unstable[i];
			C[i] = center[i] + stable[i] + unstable[i];
			D[i] = center[i] + stable[i] - unstable[i];
		} else
 		{
			D[i] = center[i] - stable[i] - unstable[i];
			C[i] = center[i] - stable[i] + unstable[i];
			B[i] = center[i] + stable[i] + unstable[i];
			A[i] = center[i] + stable[i] - unstable[i];
		}
	}

	IA = IntervalVector(A);
	IB = IntervalVector(B);
	IC = IntervalVector(C);
	ID = IntervalVector(D);
}

// -----------------------------------------------------------------

TripleSet::TripleSet(const IntervalVector& a_center, const IntervalVector& a_stable, const IntervalVector& a_unstable)
   : Icenter(a_center), Istable(a_stable), Iunstable(a_unstable), max_recursion(256)
{
  int orien = Iorientation(Icenter,Icenter + Istable,Icenter + Iunstable);

	if(orien == 0)
  {
    throw std::runtime_error("Cannot create TripleSet - colinear vectors");
  }

	int i;
	for(i = 0; i < 2; i++)
	{
      // we define  corners, so that
      // (A,B,C,D) is oriented counterclockwise
		if(orien == -1)
		{
			IA[i] = Icenter[i] - Istable[i] - Iunstable[i];
			IB[i] = Icenter[i] - Istable[i] + Iunstable[i];
			IC[i] = Icenter[i] + Istable[i] + Iunstable[i];
			ID[i] = Icenter[i] + Istable[i] - Iunstable[i];
			A[i] = IA[i].mid().leftBound();
			B[i] = IB[i].mid().leftBound();
			C[i] = IC[i].mid().leftBound();
			D[i] = ID[i].mid().leftBound();
		} else
		{
			ID[i] = Icenter[i] - Istable[i] - Iunstable[i];
			IC[i] = Icenter[i] - Istable[i] + Iunstable[i];
			IB[i] = Icenter[i] + Istable[i] + Iunstable[i];
			IA[i] = Icenter[i] + Istable[i] - Iunstable[i];
			A[i] = IA[i].mid().leftBound();
			B[i] = IB[i].mid().leftBound();
			C[i] = IC[i].mid().leftBound();
			D[i] = ID[i].mid().leftBound();
		}

		stable[i]   = Istable[i].mid().leftBound();
		unstable[i] = Iunstable[i].mid().leftBound();
		center[i]   = Icenter[i].mid().leftBound();
	}
}

// -----------------------------------------------------------------

bool TripleSet::outside(const FloatVector &point) const
// returns 1 if <vector>  does not intersect support of <this>, 0 -otherwise
{
	return (	
      (onLeft(point)) ||
		(onRight(point)) ||
		(orientation(A,B,point) == -1) ||
		(orientation(C,D,point) == -1)
	);
}

// -----------------------------------------------------------------

bool TripleSet::inside(const FloatVector &point) const
//  1 is returned if point is in the interior of support, 0 - otherwise
{
	return (
		(orientation(D,A,point) == 1)&&
		(orientation(A,B,point) == 1)&&
		(orientation(B,C,point) == 1)&&
		(orientation(C,D,point) == 1)
	);
}

// -----------------------------------------------------------------

bool TripleSet::onLeft(const FloatVector &point) const
//  the egde (DA) - is a 'left' egde - and the condition
//        for a point to be on the left side is - orientation(D,A,point)=-1
// returns 1 if <point> is in the left side (open) of N, 0 - otherwise;
{
	return (orientation(D,A,point) == -1);
}

// -----------------------------------------------------------------

/** 
BC - is the 'right' edge - the condition for the <point> to be on the right side
      is: orientation (C,B,point)=1
 returns true if <point> is in the right side (open) of N, false- otherwise;
*/
bool TripleSet::onRight(const FloatVector &point) const
{
	return (orientation(C,B,point) == 1);
}

// -----------------------------------------------------------------

bool TripleSet::mapaway(const FloatVector &point) const
{
   return (onRight(point) || onLeft(point));
}

// -----------------------------------------------------------------

/** 
true - is returned if <point> is either in the open horizonal strip
defined by 'horizontal' egdes or on the left or on the right side
both sides are open by definition
*/
bool TripleSet::across(const FloatVector &point) const
{

	if( (onLeft(point)) || (onRight(point)) ) 
		return true;

  // now we check if <point> is in the interior of the horizonatal strip defined by
  //           the egdes in N^+ - AB and CD

	return ( (orientation(A,B,point) == 1) && (orientation(C,D,point) == 1) );
}

// -----------------------------------------------------------------
/**
  the function checks an orientation of two vectors
           (v2_a - v1) and (v2_b - v1)
   we return the sign of the determinant
        |v2_a - v1 , v2_b -v1|  - here vectors are treated as collumns
  the obtained orientation can be also seen as the orientation
  of the triple  (v1,v2_a,v2_b) - positive orientation
  corresponds to counterclowise movement
*/
int TripleSet::orientation(const FloatVector& v1, const FloatVector& v2_a, const FloatVector& v2_b) const
{
	double vect_product =
			(v2_a[0]-v1[0])*(v2_b[1]-v1[1]) -
			(v2_b[0]-v1[0])*(v2_a[1]-v1[1]);
	if (vect_product > 0)    //possitive orientation - counterclokwise
		return 1;
	if (vect_product == 0)    // collinear
		return 0;
   // negative orientation - clockwise
	return -1;
}


// -----------------INTERVAL METHODS - for rigorous computations--------

/**
the egde (DA) - is a 'left' egde - and the condition  for a point to be on the left side is - orientation(D,A,point)=-1
*/
bool TripleSet::onLeft(const IntervalVector &vect) const
{
	return (Iorientation(ID,IA,vect) == -1);
}

// -----------------------------------------------------------------

/**
BC - is the 'right' edge - the condition for the <point> to be on the right side
          is: orientation (C,B,point)=1
 returns true if <vect> is in the right side (open) of N
*/
bool TripleSet::onRight(const IntervalVector &vect) const
{
	return (Iorientation(IC,IB,vect) == 1);
}

// -----------------------------------------------------------------

bool TripleSet::mapaway(const IntervalVector &vect) const
{
   return ( onLeft(vect) || onRight(vect));
}

// -----------------------------------------------------------------
/**
true is returned if point is in the interior of support
*/
bool TripleSet::inside(const IntervalVector &vect) const
{
	return (	(Iorientation(ID,IA,vect) == 1)&&
				(Iorientation(IA,IB,vect) == 1)&&
				(Iorientation(IB,IC,vect) == 1)&&
				(Iorientation(IC,ID,vect) == 1));
}

// -----------------------------------------------------------------
/**
the function checks if the segment (supp_1,supp_2) intersects the segment
           (vect_1,vect_2) - for the projection onto a plane (dim_1,dim_2)
in an interior point for both segments
if this is the case then true is returned
*/
bool TripleSet::checkIntersection(const IntervalVector& supp_1,
                                  const IntervalVector& supp_2,
                                  const IntervalVector& vect_1, 
                                  const IntervalVector& vect_2) const
{
	interval S1,S2,V1,V2,temp;
	S1 = intervalHull(supp_1[0],supp_2[0]);
	S2 = intervalHull(supp_1[1],supp_2[1]);
	V1 = intervalHull(vect_1[0],vect_2[0]);
	V2 = intervalHull(vect_1[1],vect_2[1]);

   //  (S1,S2) is an interval set - a rectangle containing supp_1,supp_2
   //  (V1,V2) is an interval set - a rectangle containing vect_1,vect_2

   // if the segments intersect , then the  rectangles  S1 x S2 and V1 x V2
   //  must intersect too, this is included to speed up the check
	if( intersection(S1,V1,temp) && intersection(S2,V2,temp) )
	{
      // now we know that the intersection is not excluded and we perform
      // a more carreful (and more time consuming) check
		int p,q,r,s;
		p = Iorientation(supp_1,supp_2,vect_1);
		q = Iorientation(supp_1,supp_2,vect_2);
		r = Iorientation(vect_1,vect_2,supp_1);
		s = Iorientation(vect_1,vect_2,supp_2);
		return ( (p*q<0) && (r*s<0) );
	}
	return false;
}

// -----------------------------------------------------------------
/**
 true- is returned if for each point, x,  in <vect>
 either one of the following conditions hold:
     - x is on the left to N
     - x is on the right to N
     - x is in support of N, but does not touch the N^+
         but to satisfy the last condition it is enough for a point to be
         in the interior of the horizontal strip defined by
         the egdes in N^+ - AB and CD
*/
bool TripleSet::across(const IntervalVector &vect) const

{
	static int rec = 0;
	rec++;
	if( (onLeft(vect)) || (onRight(vect)) )
	{
		rec--;
		return 1;
	}

//  we check if <vect> is in the interior of the horizonatal strip defined by
//           the egdes in N^+ - AB and CD
	if( (Iorientation(IA,IB,vect) == 1) && (Iorientation(IC,ID,vect) == 1) )
	{
		rec--;
		return true;
	}

  // above checks were fast and easy, but it is possible that
  // vect is still 'across' of current triple set, but it intersect
  // the left or right egde and is not in the open horizontal strip
  // defined by edges AB and DC

  // we devide current triple set onto four small sets and verify the same
  // conditions. The maximal number of recurenc is written in max_rec variable
	if(rec<max_recursion)
	{
		interval l1 = vect[0].leftBound();
		interval r1 = vect[0].rightBound();
		interval m1 = vect[0].mid();
		interval l2 = vect[1].leftBound();
		interval r2 = vect[1].rightBound();
		interval m2 = vect[1].mid();
		IntervalVector v1, v2, v3, v4;

		v1[0] = intervalHull(l1,m1);
		v1[1] = intervalHull(l2,m2);

		v2[0] = intervalHull(m1,r1);
		v2[1] = intervalHull(l2,m2);

		v3[0] = intervalHull(l1,m1);
		v3[1] = intervalHull(m2,r2);

		v4[0] = intervalHull(m1,r1);
		v4[1] = intervalHull(m2,r2);

		bool result = across(v1) && across(v2) && across(v3) && across(v4);
		rec--;
		return result;

	}else
	{
		rec--;
		return false;
	}
}

// -----------------------------------------------------------------
/**
 returns true if <vector>  does not intersect support of <this>
*/
bool TripleSet::outside(const IntervalVector &vect) const
{
	if((onLeft(vect)) ||
		(onRight(vect)) ||
		(Iorientation(IA,IB,vect) == -1) ||
		(Iorientation(IC,ID,vect) == -1)
	) 	return true;
	// what is above guaranties that the support of N has an empty intersection
	// because vect is either entirely  on left or on the right side
	// or in the open complement of the horizonal strip defined by AB and CD
	// but it is possible that neither of these conditions is satisfied
	// but still vect is outside


	interval T1, T2;
	T1 = intervalHull(IA[0],IB[0]);
	T1 = intervalHull(T1,IC[0]);
	T1 = intervalHull(T1,ID[0]);
	T2 = intervalHull(IA[1],IB[1]);
	T2 = intervalHull(T2,IC[1]);
	T2 = intervalHull(T2,ID[1]);
	//  T1 x T2 is an interval enclosure for ABCD

	return(
		vect[0] < T1 || vect[0] > T1 ||
		vect[1] < T2 || vect[1] > T2
	);
}

// -----------------------------------------------------------------
/**
returns an orientation of a triple (v1,v2,v3) 1- anticlockwise, -1 - clockwise, 0 - collinear
*/
int TripleSet::Iorientation(const IntervalVector &v1,const IntervalVector &v2,const IntervalVector& v3) const
{
	interval vect_prod = (v2[0]-v1[0])*(v3[1]-v1[1]) - (v3[0]-v1[0])*(v2[1]-v1[1]);
	if(vect_prod > 0)
		return 1; // positive orientation - anticlockwise
	if(vect_prod < 0)
		return -1; //negative orientation
   
	return 0;
}

}} // namespace capd::covrel

/// @}
