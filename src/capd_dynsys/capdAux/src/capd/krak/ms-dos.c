/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ms-dos.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/krak.h"


extern FRAME *cFrm;
extern INT fontwdth,fontHght;
INT c_fgcol,c_bgcol;

#define MYCOL(c) (c+1)

/* The following constants/procedures enable mouse use with MOUSE driver
   compliant to INT 33 rules */

static int MouseInUse=0;

void ShowCursor(void);

void InitMouse()
{
   struct REGPACK r;
   r.r_ax = 0;
   intr(0x33,&r);
   MouseInUse = r.r_ax;
   if (MouseInUse)
      ShowCursor();
}

void HideCursor()
{
   struct REGPACK r;
   r.r_ax = 2;
   intr(0x33,&r);
}

void ShowCursor()
{
   struct REGPACK r;
   r.r_ax = 1;
   intr(0x33,&r);
}

void GetPos(int *i, int *j)
{
   struct REGPACK r;
   r.r_ax = 3;
   intr(0x33,&r);
   *i = r.r_cx;
   *j = r.r_dx;
}

int GetButtons()
{
   struct REGPACK r;
   r.r_ax = 3;
   intr(0x33,&r);
   return r.r_bx & 0x7; /* bits 0, 1, 2: button L, R, M pressed */
}

void SetFgCol(col)
int col;
begin
   c_fgcol=MYCOL(col);
   setcolor(c_fgcol);
end;

void SetBgCol(col)
int col;
begin
   c_bgcol=MYCOL(col);
   setbkcolor(c_bgcol);
end;

#define DCR(a) (a>0.0)*4+(a>=1.0)*32
#define DCG(a) (a>0.0)*2+(a>=1.0)*16
#define DCB(a) (a>0.0)*1+(a>=1.0)*8
#define SC(c,r,g,b) colcode[c]=DCR(r)+DCG(g)+DCB(b)

int colcode[16]={0,1,2,3,4,5,6,7,0,1*8,2*8,3*8,4*8,5*8,6*8,7*8};

void set_col()
begin
   SC(WHITE,1.0,1.0,1.0);
   SC(BLACK,0.0,0.0,0.0);
   SC(RED,1.0,0.0,0.0);
   SC(GREEN,0.0,1.0,0.0);
   SC(BLUE,0.0,0.0,1.0);
   SC(YELLOW,1.0,1.0,0.0);
   SC(MAGENTA,1.0,0.0,1.0);
   SC(CYAN,0.0,1.0,1.0);
   SC(ORANGE,1.0,0.7,0.0);
   SC(VIOLET,0.6,0.0,0.6);
   SC(PINE,0.0,0.5,0.0);
   SC(BROWN,0.6,0.0,0.0);
   SC(OLIVE,0.6,0.6,0.0);
   SC(DARKBLUE,0.0,0.0,0.6);
   SC(ORANGERED,1.0,0.5,0.5);
   SC(BLUEGREEN,0.5,1.0,0.8);
end;

void OpenGraphics(hrs,vrs,bgcol,fgcol,ltx,lty)
int hrs,vrs,bgcol,fgcol,ltx,lty;

begin
  INT i,gd=VGA,gm=VGAHI,gr_err;
  struct palettetype pal;

  initgraph(&gd,&gm,"c:\\borlandc\\bgi");
  gr_err=graphresult();
  if (gr_err!=grOk)
  begin
    printf("graphic error %s\n",grapherrormsg(gr_err));
    exit(0);
  end;
  setactivepage(0);
  setvisualpage(0);
  InitMouse();

//  settextstyle(0,0,0);
//  setusercharsize(1,1,1,1);
  getpalette(&pal);
  if (pal.size < 16) errorExit("Not enough colors!");
  set_col();
  for(i=0;i<14;i++) setpalette(MYCOL(i),colcode[i]);

  SetBgCol(bgcol);
  SetFgCol(fgcol);
end;

void CloseGraphics()

begin
  // fgetchar();  TEMP****
  closegraph();
end;

void MoveTo(i,j)
INT i,j;

begin
  moveto(i,j);
end;

void LineTo(i,j)
INT i,j;

begin
  HideCursor();
  lineto(i,j);
  ShowCursor();
end;

void PlotDot(i,j)
INT i,j;

begin
  moveto(i,j);
//  HideCursor();
  lineto(i,j);
//  ShowCursor();
end;

void Crcl(i,j,r)
INT i,j,r;

begin
  HideCursor();
  circle(i,j,r);
  ShowCursor();
end;

void FillRct(r,pattNr,colNr)
RCT *r;
INT pattNr,colNr;

begin
  int p[10];

  p[0]=r->lti;p[1]=r->ltj;
  p[2]=r->lti;p[3]=r->rbj;
  p[4]=r->rbi;p[5]=r->rbj;
  p[6]=r->rbi;p[7]=r->ltj;
  p[8]=r->lti;p[9]=r->ltj;

  setfillpattern(patt_pntr[pattNr],MYCOL(colNr));
  setcolor(MYCOL(colNr));
  HideCursor();
  fillpoly(5,p);
  ShowCursor();
  setcolor(c_fgcol);
end;

void DrawStrng(s)
const char *s;
begin
  int x,y,i,l,solid_c=219;
  char blank[256];

  x=getx();y=gety();
  l=strlen(s);
  for (i=0;i<l;i++) blank[i]=solid_c;
  blank[l]='\0';
  HideCursor();
  setcolor(c_bgcol);
  outtext(blank);
  setcolor(c_fgcol);
  moveto(x,y);
  outtext(s);
  ShowCursor();
end;

static long tick=0,last_tick=0;

long tickClock()
begin
  long new_tick;

  new_tick=clock();
  tick+=new_tick-last_tick;
  last_tick=new_tick;
  return tick;
end;

DREAL Clock(void)
/* Function iClock returns process time in seconds as a double */
begin
  return (DREAL)tickClock()/CLK_TCK;
end;

DREAL tck2sec(long tck)
begin
  return (DREAL)tck/CLK_TCK;
end;

void GetMouse(p)
PXL *p;
begin
  int i, j;
  GetPos(&i, &j);
  p->i=i;
  p->j=j;
end;

int Button()
begin
  return GetButtons() != 0 ? 1 : 0;
end;

void Beep(INT fr,INT msec)
begin
//  sound(fr);delay(msec);nosound();
end;
char *datetime()
begin
  time_t t;

  time(&t);
  return (ctime(&t));
end;

int GetKey()
begin
  if (kbhit()) return getch(); else return NO_KEY;
end;

/// @}
