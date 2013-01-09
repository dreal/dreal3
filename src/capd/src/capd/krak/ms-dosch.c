/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ms-dosch.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifdef IBM_CH
#include <stdio.h>
#include <conio.h>
#include "capd/krak/krak.h"

extern FRAME *cFrm;
extern INT fontwdth,fontHght;
INT c_fgcol,c_bgcol;

/* The following constants/procedures enable mouse use with MOUSE driver
   compliant to INT 33 rules */

static int MouseInUse=0;

void ShowCursor(void);

void InitMouse() {
  struct REGPACK r;
  r.r_ax = 0;
  intr(0x33,&r);
  MouseInUse = r.r_ax;
  if (MouseInUse)
    ShowCursor();
  }

void HideCursor() {
  struct REGPACK r;
  r.r_ax = 2;
  intr(0x33,&r);
  }

void ShowCursor() {
  struct REGPACK r;
  r.r_ax = 1;
  intr(0x33,&r);
  }

void GetPos(int *i, int *j) {
  struct REGPACK r;
  r.r_ax = 3;
  intr(0x33,&r);
  *i = 1+r.r_cx/8;
  *j = 1+r.r_dx/8;
  }

int GetButtons() {
  struct REGPACK r;
  r.r_ax = 3;
  intr(0x33,&r);
  return r.r_bx & 0x7; /* bits 0, 1, 2: button L, R, M pressed */
  }

/*
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
*/

void OpenGraphics(hrs,vrs,bgcol,fgcol,ltx,lty)
int hrs,vrs,bgcol,fgcol,ltx,lty;

begin
  clrscr();
  InitMouse();
end;

void CloseGraphics()

begin
end;


void PlotDot(i,j)
INT i,j;

begin
end;

void Crcl(i,j,r)
INT i,j,r;

begin
end;

void FillRct(r,pattNr,colNr)
RCT *r;
INT pattNr,colNr;

begin
  int i,j;

  for (j=r->ltj;j<=r->rbj;j++)
  for (i=r->lti;i<=r->rbi;i++)
  begin
    gotoxy(i,j);printf(" ");
  end;
end;

void DrawStrng(s)
const char *s;
begin
  printf("%s",s);
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
  p->i=i-1;
  p->j=j-1;
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

#endif

/// @}
