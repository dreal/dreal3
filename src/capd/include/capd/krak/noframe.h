/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file noframe.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_NOFRAME_H_ 
#define _CAPD_KRAK_NOFRAME_H_ 

#include "capd/krak/krakSetting.h"

#ifdef WIN95
#undef circle
#endif

#if defined (WIN95) || defined (WXWIN)
#include "capd/krak/frame.h"

namespace capd{
namespace krak{
   void jump(int pixelRow,int pixelColumn);
   void draw(int pixelRow,int pixelColumn,int color=FRAME_FG);
   void drawText(const char *c,int pixelRow, int pixelColumn, int  color=FRAME_FG);
   void dot(int pixelRow,int pixelColumn,int color=FRAME_FG);
   void circ(int pixelRow,int pixelColumn,int r, int color=FRAME_FG);
   void circFill(int pixelRow,int pixelColumn,int r, int color=FRAME_FG,int pattern=SOLID_P);
   void box(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,int color=FRAME_FG);
   void boxFill(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,int color,int pattern=SOLID_P);
   void polygon(int coords[],int nPoints,int color=FRAME_FG);
   void polygonFill(int coords[],int nPoints,int color,int pattern=SOLID_P);
   void arc(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,
   int begPixelRow,int begPixelColumn,int endPixelRow,int endPixelColumn,
   int color=FRAME_FG);
   void arcFill(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,
   int begPixelRow,int begPixelColumn,int endPixelRow,int endPixelColumn,
   int color,int pattern=SOLID_P);
   void ellipse(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,int color=FRAME_FG);
   void ellipseFill(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,int col,int pattern=SOLID_P);

   void keyAndMouse(int &key, int &pixelRow, int &pixelColumn);
   void mouse(int &pixelRow, int &pixelColumn);


   void setWorldCoord(double leftBottomX,double leftBottomY, double rightTopX,double rightTopY);
   void jump(double x,double y);
   void draw(double x,double y,int color=FRAME_FG);
   void drawText(const char *c,double x, double y, int  color=FRAME_FG);
   void dot(double x,double y,int color=FRAME_FG);
   void circ(double x,double y,double r, int color=FRAME_FG);
   void circFill(double x,double y,double r, int color=FRAME_FG,int pattern=SOLID_P);
   void box(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,int color=FRAME_FG);
   void boxFill(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,int color,int pattern=SOLID_P);
   void polygon(double coords[],int nPoints,int color=FRAME_FG);
   void polygonFill(double coords[],int nPoints,int color,int pattern=SOLID_P);
   void arc(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,
   double begX,double begY,double endX,double endY,
   int color=FRAME_FG);
   void arcFill(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,
   double begX,double begY,double endX,double endY,
   int color,int pattern=SOLID_P);
   void ellipse(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,int color=FRAME_FG);
   void ellipseFill(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,int col,int pattern=SOLID_P);

   void keyAndMouse(int &key, double x,double y);
   void mouse(double x,double y);

   void clear(int color=WHITE);
   void setTextSize(int size);
   int getTextSize(void);
   void setBackgroundColor(int color);
   void setForegroundColor(int color);
   int  button(void);
   void waitButton(void);
}}

#endif

#endif // _CAPD_KRAK_NOFRAME_H_ 

/// @}
