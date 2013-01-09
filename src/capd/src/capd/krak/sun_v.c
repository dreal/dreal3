/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file sun_v.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/* This KRAK interface allows the main program to be run in background
   and collects its output in a file called "mon_file". Another
   program, "view_mon" may be used to monitior the output of the
   main program. Both the interface and the program use the module
   virtmn_i.c
   The interface is turned on with SUN_V defined
*/

#include <stdio.h>
#include <sys/ioctl.h>
#include <sys/file.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/times.h>

#include "capd/krak/krak.h"
//#include "virtmn_i.h"

#ifndef SEEK_SET
#  define SEEK_SET 0
#endif

extern FRAME *cFrm,*rootFrm;
extern INT fontwdth,fontHght;

VIRTMON VirtMon;
FILE *mon_file;
int mon_done,mon_freq;

#ifdef SUN_V

INT c_fgcol,c_bgcol;

/*____________________________________________________________________________*/

void OpenGraphics(int hrs, int vrs, int bgcol, int fgcol, INT ltx, INT lty)

begin
  int i,curr_mon=0;

/* Clear the virtual screen */

  for(i=0;i<VIRT_SCR_SIZE;i++)
    VirtMon.screen[i]=' ';
  VirtMon.prpos=0;
  VirtMon.mi=0;
  VirtMon.mj=0;
  VirtMon.but=0;

/* and copy it to "mon_file"*/

  if((mon_file=fopen("mon_file","w+b"))==NULL)
    begin
      printf("mon_file error a");
      exit(0);
    end;
  /* The structure of the file is:
     current monitor (to see the history a few last dumps are available,
    this variable points to the position of the last dump*/

  fwrite((CHAR_P)&curr_mon,sizeof(int),1,mon_file);

  /* monitoring frequency (actually monitoring period in seconds)
     shows how often the dumps should be made */

  fwrite((CHAR_P)&mon_freq,sizeof(int),1,mon_file);

  /* and finally NO_VIRT_MON dumps, originally empty */

  for (i=0;i<NO_VIRT_MON;i++)
    fwrite((CHAR_P)&VirtMon,sizeof(VIRTMON),1,mon_file);
  fclose(mon_file);

  printf("Monitor opened\n");
end;

/*____________________________________________________________________________*/

void CloseGraphics(void)

begin
end;

/*____________________________________________________________________________*/

void PlotDot(INT i, INT j)
begin
end;

/*____________________________________________________________________________*/

void Crcl(INT i, INT j, INT r)
begin
end;

/*____________________________________________________________________________*/

void FillRct(RCT *r, INT pattNr, INT colNr)
begin
end;

/*____________________________________________________________________________*/


void DrawStrng(const char *s)
begin

  while(*s!='\0' && VirtMon.prpos < VIRT_SCR_SIZE)
  VirtMon.screen[VirtMon.prpos++]=*s++;
end;

/*____________________________________________________________________________*/

static struct tms buffer;

DREAL Clock(void)
/* Function Clock returns process time in seconds as a double */
begin
  times(&buffer);
  return ((DREAL)(buffer.tms_utime+buffer.tms_stime) /60.0);
end;

/*____________________________________________________________________________*/


void GetMouse(PXL *p)
begin
  p->i=VirtMon.mi;
  p->j=VirtMon.mj;
end;

/*____________________________________________________________________________*/


int Button(void)
begin
  return VirtMon.but;
end;

/*____________________________________________________________________________*/


void Beep(INT fr,INT msec)
begin
end;

/*____________________________________________________________________________*/


struct timeval tp;

char *datetime(void)
begin
  gettimeofday(&tp,NULL);
  return (ctime(&tp.tv_sec));
//  return "date unknown\n";
end;

/*____________________________________________________________________________*/


int GetKey(void)
begin
  int ch;

  return NO_KEY;
end;

/*____________________________________________________________________________*/


#endif

//#include "virtmn_i.c"

/// @}
