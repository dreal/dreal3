/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file coord3d.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// This file prepared by Mikolaj Zalewski, June 2000.
// Not tested by others, yet.

#include "capd/krak/frame.h"
#include "capd/krak/coord3d.h"

#define CHECK if (!frm) return;
#define CHECK2(x) if (!frm) return (x);

/**
@doc
  Creates a new Coord3D object.
  @param _frm   the frame to which the coordinates are attached.
*/

capd::krak::Coord3D::Coord3D(capd::krak::Frame *_frm)
{
   frm=_frm;
   cx=0;
   cy=0;
   sc=1.0;
   CHECK;
   cx=(frm->rbi+frm->lti)/2;
   cy=(frm->rbj+frm->ltj)/2;
}

/**
@doc
  Sets the frame of the object to @i(_frm). If the frame was NULL, the center
  position is set to the center of the frame. The funcition returns the
  previous frame.
@seealso setCenter
*/
capd::krak::Frame *capd::krak::Coord3D::setFrame(capd::krak::Frame *_frm)
{
   capd::krak::Frame *tmp=frm;
   frm=_frm;
   if (!tmp)
   {
      CHECK2(tmp);
      cx=(frm->rbi+frm->lti)/2;
      cy=(frm->rbj+frm->ltj)/2;
   }
   return tmp;
}

/**
@doc
   Sets the scale of the system to @i(scale).
*/
double capd::krak::Coord3D::setScale(double scale)
{
   double tmp=sc;
   sc=scale;
   return tmp;
}

/**
@doc
  Sets the foreground color of the attached frame to @i(color). Put here for
  convenience.
*/
int capd::krak::Coord3D::setFgColor(int color)
{
   CHECK2(0);
   int tmp=frm->fgColor;
   frm->fgColor=color;
   return tmp;
}

/**
@doc
  Returns the foreground color of the attached frame. Put here for convenience.
*/
int capd::krak::Coord3D::fgColor()
{
   return (frm?frm->fgColor:0);
}

/**
@doc
  Sets the background color of the attached frame to @i(color). Put here for
  convenience.
*/
int capd::krak::Coord3D::setBgColor(int color)
{
   CHECK2(0);
   int tmp=frm->bgColor;
   frm->bgColor=color;
   return tmp;
}

/**
@doc
  Returns the background color of the attached frame. Put here for convenience.
*/
int capd::krak::Coord3D::bgColor()
{
   return (frm?frm->bgColor:0);
}

/**
@doc
  Clears the attached frame. Put here for convenience.
*/
void capd::krak::Coord3D::clear()
{
   CHECK;
   frm->Clear();
}

/**
@doc
  Sets the center (i.e. the position of the ogrin of the coordinate system)
  to (@i(i), @i(j)) (in pixel coordinates)
*/
void capd::krak::Coord3D::setCenter(int i, int j)
{
   cx=i;
   cy=j;
}

#define JUMP_FRM { \
                   CHECK \
                   int i, j; \
                   map(cpos.x, cpos.y, cpos.z, &i, &j); \
                   frm->jump(i, j); \
                 }

/**
@doc
  Jumps to the point @i(pt). Changes also the current position of the
  attached frame.
*/
void capd::krak::Coord3D::jump(const capd::krak::Point3D &pt)
{
   cpos=pt;
   JUMP_FRM;
}

/**
@doc
  Jumps to the point (@i(_x), @i(_y), @i(_z). Changes also the current
  position of the attached frame.
*/
void capd::krak::Coord3D::jump(double _x, double _y, double _z)
{
   cpos.x=_x;
   cpos.y=_y;
   cpos.z=_z;
   JUMP_FRM;
}

/**
@doc
  Draws a dot at the position (@i(x), @i(y), @i(z)). The current position is
  unaffected.
  @param color  The color of the dot. If it is FRAME_FG then the current
                foreground color is used
*/
void capd::krak::Coord3D::dot(double x, double y, double z, int color)
{
   CHECK;
   int i, j;
   map(x, y, z, &i, &j);
   frm->dot(i, j, color);
   jump(x, y, z);
}

/**
@doc
  Draws a line from the current position the position (@i(x), @i(y), @i(z). The
  current position is moved the end of the line.
  @param color  The color of the line. If it is FRAME_FG then the current
                foreground color is used
*/
void capd::krak::Coord3D::lineTo(double x, double y, double z, int color)
{
   if (!frm) jump(x, y, z);
   JUMP_FRM;     //does CHECK
   int i, j;
   map(x, y, z, &i, &j);
   frm->draw(i, j, color);
   jump(x, y, z);
}

/**
@doc
  Draws a line from the point (@i(x1), @i(y1), @i(z1)) to (@i(x2), @i(y2), @i(z2)).
  The current position is moved the end of the line.
  @param color  The color of the line. If it is FRAME_FG then the current
                foreground color is used
*/
void capd::krak::Coord3D::line(double x1, double y1, double z1,
                   double x2, double y2, double z2, int color)
{
   CHECK;
   int i1, j1, i2, j2;
   map(x1, y1, z1, &i1, &j1);
   map(x2, y2, z2, &i2, &j2);
   frm->line(i1, j1, i2, j2, color);
   jump(x2, y2, z2);
}

/**
@doc
  Draws a box with a corner in (@i(x1), @i(y1), @i(z1)) and
  and in (@i(x2), @i(y2), @i(z2)). The edges are parallel to the axis.
  The current position is moved to (@i(x2), @i(y2), @i(z2)).
  @param color  The color of the box. If it is FRAME_FG then the current
                foreground color is used
*/
void capd::krak::Coord3D::box(double x1, double y1, double z1,
                  double x2, double y2, double z2, int color)
{
   CHECK;
   line(x1, y1, z1, x2, y1, z1, color);
   line(x2, y1, z1, x2, y2, z1, color);
   line(x2, y2, z1, x1, y2, z1, color);
   line(x1, y2, z1, x1, y1, z1, color);

   line(x1, y1, z2, x2, y1, z2, color);
   line(x2, y1, z2, x2, y2, z2, color);
   line(x2, y2, z2, x1, y2, z2, color);
   line(x1, y2, z2, x1, y1, z2, color);

   line(x1, y1, z1, x1, y1, z2, color);
   line(x1, y2, z1, x1, y2, z2, color);
   line(x2, y1, z1, x2, y1, z2, color);
   line(x2, y2, z1, x2, y2, z2, color);
}

/**
@doc
  Draw a cross with in the point (@i(x), @i(y), @i(z)) and
  and in (@i(x2), @i(y2), @i(z2). The edges are parallel to the axis.
  The current position is moved to (@i(x2), @i(y2), @i(z2)).
  @param color  The color of the cross. If it is FRAME_FG then the current
                foreground color is used
*/
void capd::krak::Coord3D::Xcrss(double x, double y, double z, int size, int color)
{
   CHECK;
   int i, j;
   map(x, y, z, &i, &j);
   frm->Xcrss(i, j, size, color);
   jump(x, y, z);
}


/**
@doc
  Creates a IsomCoord3D object.
*/
capd::krak::IsomCoord3D::IsomCoord3D(capd::krak::Frame *frm, int o)
   : capd::krak::Coord3D(frm), orient(o)
{}

#define ALPHA  0.433          //(cos30)/2
#define BETA   0.250          //(sin30)/2

/**
@doc
  Maps the 3D coordinates of the point (@i(x), @i(y), @i(z)) to the
  frame pixel coordinates.
@seealso Coord3D::map
*/
void capd::krak::IsomCoord3D::map(double x, double y, double z, int *i, int *j)
{
   *i=(int) (sc*(x-(orient?-1:1)*ALPHA*z)+cx);
   *j=(int) (sc*(-y+(orient?-1:1)*BETA*z)+cy);
//  *frm<<"map ("<<x<<", "<<y<<", "<<z<<") -> ("<<*i<<", "<<*j<<")";;
}

/**
@doc
  Returns the orientation of the system
  <TABLE>
  <TR><TD>0</TD><TD>the @i(z) axis is down (@i(default))</TD></TR>
  <TR><TD>1</TD><TD>the @i(z) axis is up</TD></TR>
  </TABLE>
*/
int capd::krak::IsomCoord3D::orientation()
{
   return orient;
}

/**
@doc
  Sets the orientation of the system.<p>
  <b>Note:</b> you should use this function before drawing anything or redraw
  the screen.
  <TABLE>
  <TR><TD>0</TD><TD>the @i(z) axis is down (@i(default))</TD></TR>
  <TR><TD>1</TD><TD>the @i(z) axis is up</TD></TR>
  </TABLE>
*/
int capd::krak::IsomCoord3D::setOrientation(int i)
{
   int tmp=orient;
   orient=i;
   return tmp;
}

#define CHK_BOUND(c, f) if (c<=frm->lt##f)   \
                        {                    \
                          ai=frm->lt##f;     \
                          ls=0;              \
                        } else               \
                          if (c>=frm->rb##f) \
                          {                  \
                            ai=frm->rb##f;   \
                            rs=0;            \
                          } else ai=c;


/**
@doc
  Draws the axis of the system.
*/
void capd::krak::IsomCoord3D::drawAxis()
{
   CHECK;
   int ai, ls=1, rs=1, lz, rz, il, ir;

   CHK_BOUND(cx, i);
   frm->line(ai, frm->ltj, ai, frm->rbj, BLACK);
   if (ls) frm->line(ai-3, frm->ltj+5, ai, frm->ltj, BLACK);
   if (rs) frm->line(ai+3, frm->ltj+5, ai, frm->ltj, BLACK);

   CHK_BOUND(cy, j);
   frm->line(frm->lti, ai, frm->rbi, ai, BLACK);
   if (ls) frm->line(frm->rbi, ai, frm->rbi-5, ai-3, BLACK);
   if (rs) frm->line(frm->rbi, ai, frm->rbi-5, ai+3, BLACK);

   lz=(int) (-(BETA/ALPHA)*(frm->lti-cx)+cy);
   rz=(int) (-(BETA/ALPHA)*(frm->rbi-cx)+cy);
//  *frm<<lz<<" "<<rz<<" ";

   if (lz<=frm->ltj || rz>=frm->rbj)
      return;

   if (lz>=frm->rbj)
   {
      il=(int) ((-ALPHA/BETA)*(frm->rbj-cy)+cx);
      lz=frm->rbj;
   } else il=frm->lti;

   if (rz<=frm->ltj)
   {
      ir=(int) ((-ALPHA/BETA)*(frm->ltj-cy)+cx);
      rz=frm->ltj;
   } else ir=frm->rbi;
//  *frm<<il<<","<<lz<<" "<<ir<<","<<rz<<" ";

   frm->line(il, lz, ir, rz, BLACK);
   if (orient)
   {
      frm->line(ir, rz, ir-3, rz+6, BLACK);
      frm->line(ir, rz, ir-7, rz, BLACK);
   } else
   {
      frm->line(il, lz, il+3, lz-6, BLACK);
      frm->line(il, lz, il+7, lz, BLACK);
   }
}

/// @}
