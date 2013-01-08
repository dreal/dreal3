/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file appl-mac.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

//#include "poinc_def.h"

#ifdef MAC
 #include <stdio.h>
 #include <WindowMgr.h>
 #include <MacTypes.h>
 #include <QuickDraw.h>
 #include <FileMgr.h>
 #include <krak/unix.h>
 #include <strings.h>

 WindowPtr myWdw;
 Rect myWdw_r;

extern FRAME *cFrm;
extern INT fontWdth,fontHght;

/*___________________________________________________________________________*/

void OpenGraphics(hrs,vrs,bgcol,fgcol,ltx,lty)
int hrs,vrs,bgcol,fgcol,ltx,lty;

/* This is the internal implementation of the openGraphics function for MAC */

begin
  InitGraf(&thePort);
  InitFonts();
  InitWindows();
  InitCursor();

  SetRect(&myWdw_r,SCR_I0,SCR_J0,SCR_I0+hrs,SCR_J0+vrs);
  SetPort((myWdw=NewWindow(0L,&myWdw_r,"\p",1,1,-1L,0,0L)));
  TextSize(12);
  TextFont(22);
  TextFace(1);
  TextMode(0);
end;

/*___________________________________________________________________________*/

void CloseGraphics()

/* This is the internal implementation of the closeGraphics function for MAC.
   In case of MAC it reduces to no action.
*/

begin
end;

/*___________________________________________________________________________*/

/* MoveTo(i,j);  is implemented directly on Macintosh */

/*___________________________________________________________________________*/

/* LineTo(i,j)  is implemented directly on Macintosh */

/*___________________________________________________________________________*/

void PlotDot(i,j)
INT i,j;

/*  This is the internal implementation of the plotDot function for MAC.     */

begin
  MoveTo(i,j);
  LineTo(i,j);
end;

/*___________________________________________________________________________*/

void Crcl(i,j,r)
INT i,j,r;
begin
  Rect rc;
  SetRect(&rc,i-r,j-r,i+r,j+r);
  FrameOval(&rc);
end;

/*___________________________________________________________________________*/

/* FillRct & DrawStrng defined as Macro */

/*___________________________________________________________________________*/

/* GetMouse(*pxl) i Button() refer directly to Macintosh */

/*___________________________________________________________________________*/

/* Clock() defined as Macro */

/*___________________________________________________________________________*/

void Beep(freq,time)
INT freq,time;
begin
  SysBeep(2);
end;

/*___________________________________________________________________________*/

char *datetime()
begin
return ("date/time unknown\n");
end;

/*___________________________________________________________________________*/

/* This was intended to be a full implementation of Beep on MAC but it
   does not work.
static INT soundBuf[]={-1,0,255,0,0,0,0};

void Beep(freq,time)
INT freq,time;
begin
  soundBuf[1]=783360/freq;
  soundBuf[3]=(6*time)/100;
  StartSound(soundBuf,(long)9,(long)(-1));
end;
*/

/*___________________________________________________________________________*/

#endif

/// @}
