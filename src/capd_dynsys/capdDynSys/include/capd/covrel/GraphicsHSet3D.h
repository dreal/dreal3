/// @addtogroup covrel
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file GraphicsHSet3D.h
///
/// @author Daniel Wilczak
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_COVREL_GRAPHICSHSET3D_H_ 
#define _CAPD_COVREL_GRAPHICSHSET3D_H_ 

#include "capd/krak/krak.h"
#include "capd/krak/coord3d.h"
#include "capd/covrel/HSet3D.h"

namespace capd{
namespace covrel{

class GraphicsHSet3D : public HSet3D{
public:
  typedef HSet3D::FloatVector FloatVector;
  typedef HSet3D::IntervalVector IntervalVector;
  typedef HSet3D::FloatMatrix FloatMatrix;
  typedef HSet3D::IntervalMatrix IntervalMatrix;

  GraphicsHSet3D(){}
  GraphicsHSet3D(const FloatVector &Center, const FloatVector &U, const FloatVector &S1, const FloatVector &S2)
    : HSet3D(Center,U,S1,S2){}
  GraphicsHSet3D(const IntervalVector &Center, const IntervalVector &U, const IntervalVector &S1, const IntervalVector &S2)
    : HSet3D(Center,U,S1,S2){}
  ~GraphicsHSet3D(){}

  void show(Frame &f, int dim1, int dim2) const;
  void show(Frame &f, int dim1, int dim2, const IntervalVector &, int color=BLACK) const;
  void show(Coord3D &f) const;
  void show(Coord3D &f, const IntervalVector &iv, int color=BLACK) const;
  friend Coord3D& operator << (Coord3D &, const GraphicsHSet3D&);
};

}} // namespace capd::covrel

#endif // _CAPD_COVREL_GRAPHICSHSET3D_H_ 

/// @}
