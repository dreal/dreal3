/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file color.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include "capd/krak/frame.h"

namespace capd{
namespace krak{
char colorname[24][24]={"white","black","red","green",
                        "blue","yellow","magenta","cyan",
                        "orange","violet","pine","brown",
                        "olive","darkblue","orangered","bluegreen",
                        "x1","x2","x3","x4","x5","x6","x7","x8"
                       };
int gray[24]={ BLUEGREEN,WHITE,ORANGE,YELLOW,
               CYAN,OLIVE,GREEN,VIOLET,
               MAGENTA,PINE,ORANGERED,RED,
               BROWN,BLUE,DARKBLUE,BLACK,
               16,17,18,19,20,21,22,23
             };
float red_c[MAX_PALETTE],green_c[MAX_PALETTE],blue_c[MAX_PALETTE];

}}

#define SetColor(c,r,g,b) red_c[c]=r;green_c[c]=g;blue_c[c]=b;

int off0,off1=40,off2=45,off3=15,off4=15,off5=30,off6=30,off7=25;
//int off,off1=40,off2=40,off3=40,off4=40,off5=40;
namespace capd{
namespace krak{
double tr_cubic(double t)
{
   return  4*(t-0.5)*(t-0.5)*(t-0.5)+0.5;
}
/*____________________________________________________________________________*/

void set_colors(void)
{
   int i;
   double t;
   double a[3]={0.7, 0.0, 0.0},
          b[3]={1.0, 0.5, 0.0},
          c[3]={0.9, 0.9, 0.0},
          d[3]={0.4, 1.0, 0.4},
          e[3]={0.0, 1.0, 1.0},
          f[3]={0.5, 0.5, 1.0},
          g[3]={0.0, 0.0, 0.7},
          h[3]={0.7, 0.0, 0.7};

   SetColor(WHITE,1.0,1.0,1.0);
   SetColor(BLACK,0.0,0.0,0.0);
   SetColor(RED,1.0,0.0,0.0);
   SetColor(GREEN,0.0,1.0,0.0);
   SetColor(BLUE,0.0,0.0,1.0);
   SetColor(YELLOW,1.0,1.0,0.0);
   SetColor(MAGENTA,1.0,0.0,1.0);
   SetColor(CYAN,0.0,1.0,1.0);
   SetColor(ORANGE,1.0,0.7,0.0);
   SetColor(VIOLET,0.6,0.0,0.6);
   SetColor(PINE,0.0,0.5,0.0);
   SetColor(BROWN,0.7,0.3,0.0);
   SetColor(OLIVE,0.6,0.6,0.0);
   SetColor(DARKBLUE,0.0,0.0,0.6);
   SetColor(ORANGERED,1.0,0.5,0.5);
   SetColor(BLUEGREEN,0.5,1.0,0.8);

#  if(MAX_PALETTE>=216)
{
   off0=16;
   for (i=0;i<off1;i++)
   {
      t=i/(double)off1;

#      define resc(t) t
      SetColor(i+off0, (1-(resc(t)))*a[0]+(resc(t))*b[0],
         (1-(resc(t)))*a[1]+(resc(t))*b[1], (1-(resc(t)))*a[2]+(resc(t))*b[2] ) ;
   }

   off0=off0+off1;
   for (i=0;i<off2;i++)
   {
      t=i/(double)off2;
#      undef resc
#      define resc(t) -t*t+2*t
//  (4*(t-0.5)*(t-0.5)*(t-0.5)+0.5 + 2*t + (2*t-t*t))/4
      SetColor(i+off0,  (1-(resc(t)))*b[0]+(resc(t))*c[0],
         (1-(resc(t)))*b[1]+(resc(t))*c[1], (1-(resc(t)))*b[2]+(resc(t))*c[2] ) ;
   }

   off0=off0+off2;
   for (i=0;i<off3;i++)
   {
      t=i/(double)off3;
#      undef resc
#      define resc(t) t
//  ( t*t + t )/2
      SetColor(i+off0,  (1-(resc(t)))*c[0]+(resc(t))*d[0],
         (1-(resc(t)))*c[1]+(resc(t))*d[1], (1-(resc(t)))*c[2]+(resc(t))*d[2] ) ;
   }

   off0=off0+off3;
   for (i=0;i<off4;i++)
   {
      t=i/(double)off4;
#     undef resc
#     define resc(t) t
      SetColor(i+off0, (1-(resc(t)))*d[0]+(resc(t))*e[0],
         (1-(resc(t)))*d[1]+(resc(t))*e[1], (1-(resc(t)))*d[2]+(resc(t))*e[2] ) ;
   }

   off0=off0+off4;
   for (i=0;i<off5;i++)
   {
      t=i/(double)off5;
#     undef resc
#     define resc(t) t
      SetColor(i+off0, (1-(resc(t)))*e[0]+(resc(t))*f[0],
         (1-(resc(t)))*e[1]+(resc(t))*f[1], (1-(resc(t)))*e[2]+(resc(t))*f[2] ) ;
   }

   off0=off0+off5;
   for (i=0;i<off6;i++)
   {
      t=i/(double)off6;
#     undef resc
#     define resc(t) t
//(tr_cubic(t)+(-t*t+2*t))/2
      SetColor(i+off0, (1-(resc(t)))*f[0]+(resc(t))*g[0],
         (1-(resc(t)))*f[1]+(resc(t))*g[1], (1-(resc(t)))*f[2]+(resc(t))*g[2] ) ;
   }

   off0=off0+off6;
   for (i=0;i<off7;i++)
   {
      t=i/(double)off7;
#     undef resc
#     define resc(t) t
      SetColor(i+off0, (1-(resc(t)))*g[0]+(resc(t))*h[0],
         (1-(resc(t)))*g[1]+(resc(t))*h[1], (1-(resc(t)))*g[2]+(resc(t))*h[2] ) ;
   }
   }
# endif
#  if(MAX_PALETTE>=316)
for(int i=0;i<100;++i){
  float f=(float)(i)/100.;
  SetColor(216+i,f,f,f);
}
# endif
}


/*____________________________________________________________________________*/
/*
void blond(float s)

begin
  int i;

  for (i=0;i<16;i++)
  begin
   red_b[i]=red_a[i]+s*(1.0-red_a[i]);
    green_b[i]=green_a[i]+s*(1.0-green_a[i]);
    blue_b[i]=blue_a[i]+s*(1.0-blue_a[i]);
  end;
end;
*/
/*____________________________________________________________________________*/
/*
void dark(float s)
begin
  int i;

  s=1.0-s;
  for (i=0;i<16;i++)
  begin
    red_b[i]=red_a[i]*s;
    green_b[i]=green_a[i]*s;
    blue_b[i]=blue_a[i]*s;
  end;
end;

*/
/*____________________________________________________________________________*/

}}

/// @}
