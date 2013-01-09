/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file noframe.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/noframe.h"

#if defined (WIN95) || defined (WXWIN)
/*  Warning:
    Krak uses the convention of pixel coordinates in the form (column,row)
    noFrame reverses it to (row,column) to make it consistent
    with the (row,column) coordinates for printing
*/

namespace capd{
namespace krak{

void jump(int pixelRow,int pixelColumn)
{
   rootFrm->jump(pixelColumn,pixelRow);
}

void draw(int pixelRow,int pixelColumn,int color)
{
   rootFrm->draw(pixelColumn,pixelRow,color);
}
void drawText(const char *c,int pixelRow,int pixelColumn,int color)
{
   rootFrm->drawText(c,pixelColumn,pixelRow,color);
   // sadjhf;
}
void dot(int pixelRow,int pixelColumn,int color)
{
   rootFrm->dot(pixelColumn,pixelRow,color);
}
void circ(int pixelRow,int pixelColumn,int r, int color)
{
   rootFrm->ellipse(pixelColumn-r,pixelRow-r,pixelColumn+r,pixelRow+r,color);
}
void circFill(int pixelRow,int pixelColumn,int r, int color, int pattern)
{
   rootFrm->ellipseFill(pixelColumn-r,pixelRow-r,pixelColumn+r,pixelRow+r,color,pattern);
}
void box(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,int color)
{
   rootFrm->box(leftTopPixelColumn,leftTopPixelRow, rightBottomPixelColumn,rightBottomPixelRow,color);
}
void boxFill(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,int color,int pattern)
{
   rootFrm->boxFill(leftTopPixelColumn,leftTopPixelRow,
      rightBottomPixelColumn,rightBottomPixelRow,color,pattern);
}
void polygon(int coords[],int nPoints,int color)
{
   int *locCoords = (int *)malloc(2*nPoints*sizeof(int));
   int i;
   for(i=0;i<nPoints;i++)
   {
      locCoords[i+i+1]=coords[i+i];
      locCoords[i+i]=coords[i+i+1];
   }
   rootFrm->polygon(locCoords,nPoints,color);
}
void polygonFill(int coords[],int nPoints,int color,int pattern)
{
   int *locCoords = (int *)malloc(2*nPoints*sizeof(int));
   int i;
   for(i=0;i<nPoints;i++)
   {
      locCoords[i+i+1]=coords[i+i];
      locCoords[i+i]=coords[i+i+1];
   }
   rootFrm->polygonFill(locCoords,nPoints,color);
}
void arc(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,
   int begPixelRow,int begPixelColumn,int endPixelRow,int endPixelColumn,
   int color)
{
   rootFrm->arc(leftTopPixelColumn,leftTopPixelRow,
      rightBottomPixelColumn,rightBottomPixelRow,
      begPixelColumn,begPixelRow,endPixelColumn,endPixelRow,
      color);
}
void arcFill(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,
   int begPixelRow,int begPixelColumn,int endPixelRow,int endPixelColumn,
   int color,int pattern)
{
   rootFrm->arcFill(leftTopPixelColumn,leftTopPixelRow,
      rightBottomPixelColumn,rightBottomPixelRow,
      begPixelColumn,begPixelRow,endPixelColumn,endPixelRow,
      color,pattern);
}
void ellipse(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,int color)
{
   rootFrm->ellipse(leftTopPixelRow,leftTopPixelColumn,
      rightBottomPixelRow,rightBottomPixelColumn,color);
}
void ellipseFill(int leftTopPixelRow,int leftTopPixelColumn,
   int rightBottomPixelRow,int rightBottomPixelColumn,int color,int pattern)
{
   rootFrm->ellipseFill(leftTopPixelRow,leftTopPixelColumn,
      rightBottomPixelRow,rightBottomPixelColumn,color,pattern);
}

static capd::krak::UserMove um;
static capd::krak::Pxl pix;
void keyAndMouse(int &key, int &pixelRow, int &pixelColumn)
{
   GetUserMove(um);
   key=um.key;
   pixelRow=um.pxl.j;
   pixelColumn=um.pxl.i;
}
void mouse(int &pixelRow, int &pixelColumn)
{
   GetMouse(&pix);
   pixelRow=pix.j;
   pixelColumn=pix.i;
}

void setWorldCoord(double leftBottomX,double leftBottomY, double rightTopX,double rightTopY)
{
   rootFrm->setWorldCoord(leftBottomX,leftBottomY,rightTopX,rightTopY);
}
void jump(double x,double y)
{
   rootFrm->jump(x,y);
}
void draw(double x,double y,int color)
{
   rootFrm->draw(x,y,color);
}
void drawText(const char *c,double x, double y, int  color)
{
   rootFrm->drawText(c,x,y,color);
}
void dot(double x,double y,int color)
{
   rootFrm->dot(x,y,color);
}
void circ(double x,double y,double r, int color)
{
   rootFrm->ellipse(x-r,y-r,x+r,y+r,color);
}
void circFill(double x,double y,double r, int color, int pattern)
{
   rootFrm->ellipseFill(x-r,y-r,x+r,y+r,color,pattern);
}
void box(double leftBottomX,double leftBottomY, double rightTopX,double rightTopY,int color)
{
   rootFrm->box(leftBottomX,leftBottomY,rightTopX,rightTopY,color);
}
void boxFill(double leftBottomX,double leftBottomY, double rightTopX,double rightTopY,int color,int pattern)
{
   rootFrm->boxFill(leftBottomX,leftBottomY,rightTopX,rightTopY,color,pattern);
}
void polygon(double coords[],int nPoints,int color)
{
   rootFrm->polygon(coords,nPoints,color);
}
void polygonFill(double coords[],int nPoints,int color,int pattern)
{
   rootFrm->polygonFill(coords,nPoints,color,pattern);
}
void arc(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,
   double begX,double begY,double endX,double endY,
   int color)
{
   rootFrm->arc(leftBottomX,leftBottomY,rightTopX,rightTopY,begX,begY,endX,endY,color);
}
void arcFill(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,
   double begX,double begY,double endX,double endY,
   int color,int pattern)
{
   rootFrm->arcFill(leftBottomX,leftBottomY,rightTopX,rightTopY,begX,begY,endX,endY,color,pattern);
}
void ellipse(double leftBottomX,double leftBottomY, double rightTopX,double rightTopY,int color)
{
   rootFrm->ellipse(leftBottomX,leftBottomY,rightTopX,rightTopY,color);
}
void ellipseFill(double leftBottomX,double leftBottomY,
   double rightTopX,double rightTopY,int color,int pattern)
{
   rootFrm->ellipseFill(leftBottomX,leftBottomY,rightTopX,rightTopY,color,pattern);
}

void keyAndMouse(int &key, double &x,double &y)
{
   int pixelRow,pixelColumn;
   keyAndMouse(key,pixelRow,pixelColumn);
   x=rootFrm->i2x(pixelColumn);
   y=rootFrm->j2y(pixelRow);
}

void mouse(double &x,double &y)
{
   int pixelRow,pixelColumn;
   mouse(pixelRow,pixelColumn);
   x=rootFrm->i2x(pixelColumn);
   y=rootFrm->j2y(pixelRow);
}


void clear(int color)
{
   rootFrm->Clear(color);
}
void setTextSize(int size)
{
   SetTextSize(size);
}
int getTextSize(void)
{
   return GetTextSize();
}
void setBackgroundColor(int color)
{
   rootFrm->SetBgColor(color);
}
void setForegroundColor(int color)
{
   rootFrm->SetFgColor(color);
}
int  button(void)
{
   return Button();
}
void waitButton(void)
{
   waitBt();
}
}} // the end of the namespace capd::krak
#endif

/// @}
