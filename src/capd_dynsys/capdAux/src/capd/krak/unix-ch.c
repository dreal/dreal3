/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file unix-ch.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifdef UNIX_TXT

#include "capd/krak/krak.h"
#include <stdio.h>
#include <curses.h>
#include <fcntl.h>
#include <sys/time.h>
#include <sys/times.h>

extern FRAME *cFrm;
extern INT fontwdth,fontHght;
INT c_fgcol,c_bgcol;

/* for mouse simulation */

#define MOUSE_SYMBOL '#'

static INT x_position,y_position;
static INT leftBoundutton,rightBoundutton,middle_button;
static INT char_buffer;
static INT under_mouse_symbol;

#define EMPTY '\0'

/*----------------------------------------------------------------------------*/

void InitMouse() {
   leftBoundutton=0;
   rightBoundutton=0;
   middle_button=0;
  }

/*----------------------------------------------------------------------------*/

void Simulate_Mouse() {

  INT char1;
  static INT first_call=0;

  if(!first_call)
   {
    first_call=1;
    under_mouse_symbol=inch();
    addch(MOUSE_SYMBOL);
    refresh();
    move(y_position,x_position);
    refresh();
   }

  move(y_position,x_position);
  refresh();

  char1=GetKey();
  if(char1!=NO_KEY)
   {
    if(char1=='l')
      {
       leftBoundutton=1;
       return;
      }
    if(char1=='r')
      {
       rightBoundutton=1;
       return;
      }
    if(char1=='m')
      {
       middle_button=1;
       return;
      }

    leftBoundutton=rightBoundutton=middle_button=0;

    if(char1==27)
     {
      char_buffer=EMPTY;
      char1=GetKey();
      if(char1==91) char1=GetKey();
      switch(char1)
 {
  case 65: /* up key */
   if(y_position>0)
    {
     addch(under_mouse_symbol);
     refresh();
     --y_position;
     move(y_position,x_position);
     refresh();
     under_mouse_symbol=inch();
     addch(MOUSE_SYMBOL);
     refresh();
     move(y_position,x_position);
     refresh();
                  }
                 break;
         case 66: /* down key */
   if(y_position<LINES-1)
    {
     addch(under_mouse_symbol);
     refresh();
     ++y_position;
     move(y_position,x_position);
     refresh();
     under_mouse_symbol=inch();
     addch(MOUSE_SYMBOL);
     refresh();
     move(y_position,x_position);
     refresh();
    }
   break;
  case 67: /* right key */
   if(x_position<COLS-1)
    {
     addch(under_mouse_symbol);
     refresh();
     ++x_position;
     move(y_position,x_position);
     refresh();
     under_mouse_symbol=inch();
     addch(MOUSE_SYMBOL);
     refresh();
     move(y_position,x_position);
     refresh();
    }
   break;
  case 68: /* left key */
   if(x_position>0)
    {
     addch(under_mouse_symbol);
     refresh();
     --x_position;
     move(y_position,x_position);
     refresh();
     under_mouse_symbol=inch();
     addch(MOUSE_SYMBOL);
     refresh();
     move(y_position,x_position);
     refresh();
    }
   break;
 }  /* for switch*/
     }   /* for char1==27*/

   }   /* for char1!=NO_KEY*/

  }
/*----------------------------------------------------------------------------*/

void HideCursor() {
  }

/*----------------------------------------------------------------------------*/

void ShowCursor() {
  }

/*----------------------------------------------------------------------------*/

void GetPos(int *i, int *j) {

  *i=x_position;
  *j=y_position;
  }

/*----------------------------------------------------------------------------*/

int GetButtons() {
  INT temp;

  temp=0;
  if(leftBoundutton) temp+=1;
  if(rightBoundutton) temp+=2;
  if(middle_button) temp+=4;

  leftBoundutton=rightBoundutton=middle_button=0;

  return temp & 0x7; /* bits 0, 1, 2: button L, R, M pressed */
  }

/*----------------------------------------------------------------------------*/

void OpenGraphics(INT hrs,INT vrs,INT bgcol,INT fgcol, INT ltx, INT lty)

begin
  initscr();
  crmode();
  noecho();
  refresh();
  clear();
  x_position=15;
  y_position=2;
  move(y_position,x_position);
  refresh();
  InitMouse();
  char_buffer=EMPTY;
end;

/*----------------------------------------------------------------------------*/

void CloseGraphics()

begin
  nocrmode();
  echo();
  refresh();
  endwin();
end;

/*----------------------------------------------------------------------------*/

void PlotDot(INT i,INT j)

begin
end;

/*----------------------------------------------------------------------------*/

void Crcl(INT i,INT j,INT r)

begin
end;

/*----------------------------------------------------------------------------*/

void FillRct(RCT *r,INT pattNr,INT colNr)

begin
 int i,j;

 clear();
 refresh();

 /* for(i=(r->ltj);i<=(r->rbj);i++)
  for(j=(r->lti);j<=(r->rbi);j++)
   {
    move(j,i);
    refresh();
    addch(' ');
    refresh();
   }*/

under_mouse_symbol=' ';
end;

/*----------------------------------------------------------------------------*/

void DrawStrng(const char *s)

begin
  printw("%s",s);
  refresh();
end;

/*----------------------------------------------------------------------------*/

static struct tms buffer;

DREAL Clock()
begin
  times(&buffer);
  return ((DREAL)(buffer.tms_utime+buffer.tms_stime) /60.0);
end;

/*____________________________________________________________________________*/

struct timeval tp;

DREAL RClock(void)
begin
  gettimeofday(&tp,NULL);
  return ((DREAL)tp.tv_sec);
end;

/*----------------------------------------------------------------------------*/

void GetMouse(PXL *p)

begin
  int i, j;

  Simulate_Mouse();
  GetPos(&i, &j);
  p->i=i-1;
  p->j=j-1;
end;

/*----------------------------------------------------------------------------*/

int Button()
begin

  Simulate_Mouse();
  return GetButtons() != 0 ? 1 : 0;
end;

/*----------------------------------------------------------------------------*/

void Beep(INT fr,INT msec)
begin
end;

/*____________________________________________________________________________*/

struct timeval tp;

char *datetime(void)
begin
  gettimeofday(&tp,NULL);
  return (ctime(&tp.tv_sec));
end;

/*----------------------------------------------------------------------------*/
/* you should set noecho mode and crmode mode on your terminal using curses */
/* function to use this function                                            */

int kbhit()
begin

 int flags;

 if(char_buffer!=EMPTY)
  return char_buffer;

 /* In SUN UNIX O_NONBLOCK is equal O_NDELAY */
 flags=fcntl(0,F_GETFL,0);
 fcntl(0,F_SETFL,flags|O_NONBLOCK);
 char_buffer=getch();
 fcntl(0,F_SETFL,flags&~O_NONBLOCK);
 if(char_buffer<0) char_buffer=EMPTY;
 return char_buffer;

end;

/*----------------------------------------------------------------------------*/

int GetKey()
begin

  INT temp;

  if (kbhit())
   {
    temp=char_buffer;
    char_buffer=EMPTY;
    return temp;
   }
  else return NO_KEY;

end;

/*----------------------------------------------------------------------------*/

#endif

/// @}
