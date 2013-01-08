/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file GraphicsTripleSet.cpp
///
/// @author Jaroslaw Dulak, Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/covrel/GraphicsTripleSet.h"

namespace capd{
namespace covrel{

typedef GraphicsTripleSet::FloatVector FloatVector;
typedef GraphicsTripleSet::IntervalVector IntervalVector;


void GraphicsTripleSet::show(Frame &f) const
{
  // plotting in Yellow - the N^- edges - but for better visualition
  FloatVector S = center + unstable - 2.*stable;
  FloatVector E = center + unstable + 2.*stable;
  f.line(S[0],S[1],E[0],E[1],YELLOW);

  S = center - unstable - 2.*stable;
  E = center - unstable + 2.*stable;
  f.line(S[0],S[1],E[0],E[1],YELLOW);

   // plotting of the support
	f.jump(A[0],A[1]);
	f.draw(B[0],B[1]);
	f.draw(C[0],C[1]);
	f.draw(D[0],D[1]);
	f.draw(A[0],A[1]);

   // plotting the stable direction in BLUE
	f.jump(center[0],center[1]);
	f.draw(center[0] + stable[0],center[1] + stable[1],BLUE);

   // plotting the unstable direction in RED
	f.jump(center[0],center[1]);
	f.draw(center[0] + unstable[0],center[1] + unstable[1],RED);
}

// -----------------------------------------------------------------

void GraphicsTripleSet::show(Frame &f, const FloatVector& point, int color) const
{
	show(f);													//we plot support
	f.Xcrss(point[0],point[1],5,color);  //we plot the point
}

// -----------------------------------------------------------------

void GraphicsTripleSet::show(Frame &f, const IntervalVector& vect, int color) const
{
	show(f);
	f.boxFill(vect[0].leftBound(),vect[1].leftBound(),vect[0].rightBound(),vect[1].rightBound(),color);
	f.box(vect[0].leftBound(),vect[1].leftBound(),vect[0].rightBound(),vect[1].rightBound(),BLACK);
}

// -----------------------------------------------------------------

Frame& operator<<(Frame& f, GraphicsTripleSet& Set)
{
   Set.show(f);
	return f;
}

}} // namespace capd::covrel

/// @}
