/////////////////////////////////////////////////////////////////////////////
/// @file coord3d.h
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

#ifndef _CAPD_KRAK_COORD3D_H_ 
#define _CAPD_KRAK_COORD3D_H_ 

#include <stdlib.h>
#include "capd/krak/color.h"



namespace capd{
namespace krak{
  /**
@doc<Coord3D::%descr>
  This is a base class for 3D drawing functions. This is a abstract
  class. The @ref<IsomCoord3D::%top>(IsomCoord3D) class implements
  the isometric 3D drawing functions.
*/
struct Point3D
{
   double x, y, z;
   Point3D(double _x=0, double _y=0, double _z=0) :x(_x), y(_y), z(_z) {}
};

class Frame;

class Coord3D
{
public:
   Coord3D(capd::krak::Frame *_frm=NULL);
   virtual ~Coord3D() {}

  /**
  @doc<Coord3D::Frame *frame()>
    Returns the frame to which the object is attached.
  */
   capd::krak::Frame *frame() {return frm;}
   capd::krak::Frame *setFrame(capd::krak::Frame *f);
   void setCenter(int i, int j);

  /**
  @doc<Coord3D::double scale()>
    Returns the scale (the factor which is used when translating
    3D coordinates to pixels)
  */
   double scale() {return sc;}
   double setScale(double s);

  /**
  @doc<Coord3D::void map(double, double, double, int *, int *)>
    Maps the 3D coordinates of the point (@i(x), @i(y), @i(z)) to the
    frame pixel coordinates (this is a pure virtual function in Coord3D.
    Implemented in @ref<IsomCoord3D::%top>(IsomCoord3D))
  */
   virtual void map(double x, double y, double z, int *i, int *j)=0;
  /**
  @doc<Coord3D::void map(const Point3D &, int *, int *)>
    Maps the 3D coordinates of the point @i(p) to the
    frame pixel coordinates (this is a pure virtual function in Coord3D.
    Implemented in @ref<IsomCoord3D::%top>(IsomCoord3D))
  */
   void map(const Point3D &p, int *i, int *j)
   {
      map(p.x, p.y, p.z, i, j);
   }

   int fgColor();
   int setFgColor(int fc);
   int bgColor();
   int setBgColor(int bc);

   virtual void clear();

  /**
  @doc<Coord3D::Point3D pos()>
    Returns the current position.
  */
   Point3D pos() {return cpos;}
   virtual void jump(const Point3D &pt);
   virtual void jump(double x, double y, double z);

   virtual void dot(double x, double y, double z, int color=FRAME_FG);
  /**
  @doc<Coord3D::void dot(const Point3D &, int)>
    Draws a dot at the position (@i(p)). The current position is
    unaffected.
    @param color  The color of the dot. If it is FRAME_FG then the current
                  foreground color is used
  */
   void dot(const Point3D &p, int color=FRAME_FG)
   {
      dot(p.x, p.y, p.z, color);
   }

   virtual void lineTo(double x, double y, double z, int color=FRAME_FG);
  /**
  @doc<Coord3D::void lineTo(const Point3D &, int)>
    Draws a line from the current position the position (@i(p). The
    current position is moved the end of the line.
    @param color  The color of the line. If it is FRAME_FG then the current
                  foreground color is used
  */
   void lineTo(const Point3D &p, int color=FRAME_FG)
   {
      lineTo(p.x, p.y, p.z, color);
   }

   virtual void line(double x1, double y1, double z1, double x2, double y2, double z2,
         int color=FRAME_FG);
  /**
  @doc<Coord3D::void line(const Point3D &, const Point3D &, int)>
    Draws a line from the point @i(p1) to @i(p2).
    The current position is moved the end of the line.
    @param color  The color of the line. If it is FRAME_FG then the current
                  foreground color is used
  */
   void line(const Point3D &p1, const Point3D &p2, int color=FRAME_FG)
   {
      line(p1.x, p1.y, p1.z, p2.x, p2.y, p2.z, color);
   }

   virtual void box(double x1, double y1, double z1, double x2, double y2, double z2,
         int color=FRAME_FG);
  /**
  @doc<Coord3D::void box(const Point3D &, const Point3D &, int)>
    Draws a box with a corner in @i(p1) and
    and in @i(p2). The edges are parallel to the axis.
    The current position is moved to @i(p2).
    @param color  The color of the box. If it is FRAME_FG then the current
                  foreground color is used
  */
   void box(const Point3D &p1, const Point3D &p2, int color=FRAME_FG)
   {
      box(p1.x, p1.y, p1.z, p2.x, p2.y, p2.z, color);
   }

   virtual void Xcrss(double x, double y, double z, int size=1, int color=FRAME_FG);
   void Xcrss(const Point3D &p, int size=1, int color=FRAME_FG)
   {
      Xcrss(p.x, p.y, p.z, size, color);
   }

  /**
  @doc<Coord3D::void drawAxis()>
    Draws the axis of the system. (this is a pure virtual function in Coord3D.
    Implemented in IsomCoord3D)
  */
   virtual void drawAxis()=0;

protected:
   capd::krak::Frame *frm;
   int cx, cy;
   Point3D cpos;
   double sc;
};

/**
@doc<IsomCoord3D::%descr>
  This is a class for isomteric 3D drawing. Most function are inherited
  from @ref<Coord3D::%top>(Coord3D).<p>
  Example use:
  <pre>
    IsomCoord3D c(frm);      // c will draw on the frame frm
    c.setFgColor(BLACK);     // this function sets the color of
                             // the attached frame
    c.setScale(0.1);         // this sets the size of a logical unit

    c.jump(15.2, 17, 44);
    c.lineTo(33.2, 32, 45);
    c.box(45, 56, 67,
          -123, -23, -56, RED);
    //etc...
  </pre>
*/

class IsomCoord3D : public Coord3D
{
public:
   IsomCoord3D(capd::krak::Frame *frm=NULL, int orient=0);
   virtual ~IsomCoord3D() {}
   virtual int orientation();
   virtual int setOrientation(int i);
   virtual void map(double x, double y, double z, int *i, int *j);
   virtual void drawAxis();

protected:
   int orient;
};

}} // the end of the namespace capd::krak

#endif // _CAPD_KRAK_COORD3D_H_ 
