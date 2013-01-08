/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ms-win31.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/krak.h"

#include <conio.h>
#include <dos.h>

#define MAKERGB(c)\
  RGB(\
    ((BYTE)(255*red_c[c%MAX_COLOR_NO])),\
    ((BYTE)(255*green_c[c%MAX_COLOR_NO])),\
    ((BYTE)(255*blue_c[c%MAX_COLOR_NO])))

#ifdef BLACKWHITE
#  define TRANSLATE_COLOR(c) GetNearestColor(hdc,MAKERGB(c!=WHITE))
#else
#  define TRANSLATE_COLOR(c)\
((use_palette) ?  (PALETTEINDEX(c)) :  (MAKERGB(c)))
//  ((use_palette) ?  (PALETTEINDEX(c+20)) :  GetNearestColor(hdc,(MAKERGB(c))))
#endif
#define SEPARATOR ';'
int use_palette=1;

extern FRAME *cFrm,*rootFrm;
extern INT fontWdth,fontHght;
extern int what_restore=0;

char emptytext[]="";

int nCmdShow;
HDC  hdc;
WORD ioff,joff,ncol;
DWORD ijoff;
HWND hwnd ;
HINSTANCE hInstance,hPrevInstance;

LOGBRUSH lb;
HBRUSH nullhbr, hbrOld;

HPALETTE hpal=NULL,hPalPrevious;
LOGPALETTE *plgpl;

HFONT hfont, hfontOld;
PLOGFONT plf;

HBITMAP hbmp_pat[MAX_PATTERN_NO];

INT c_bgcol,c_fgcol;
extern float red_c[MAX_PALETTE],green_c[MAX_PALETTE],blue_c[MAX_PALETTE];

static int ButtonState=0;


/*___________________________________________________________________________*/

void EmptyMQueue()
begin
  MSG msg;

  while (PeekMessage(&msg, NULL, 0, 0, PM_REMOVE))
  begin
    if(msg.message == WM_QUIT) exit(0);
    TranslateMessage(&msg);
    DispatchMessage(&msg);
  end;
end;

/*___________________________________________________________________________*/

void restore_window_settings(hwnd,hdc)
HDC hdc;
HWND hwnd;

begin
  long i;

  ijoff=GetDCOrg(hdc);
  ioff=LOWORD(ijoff); joff=HIWORD(ijoff);
end;

void restore_window_attributes(hwnd,hdc)
HDC hdc;
HWND hwnd;

begin
  SetMapMode(hdc, MM_TEXT);

  hfontOld = SelectObject(hdc, hfont);

  if(hpal!=NULL)
  begin
  hPalPrevious = SelectPalette(hdc, hpal, FALSE);
  if ((ncol=RealizePalette(hdc)) == NULL);

//  MessageBox(hwnd, "Can't realize palette", "Error", MB_OK);

  SetBkColor(hdc,TRANSLATE_COLOR(c_bgcol));
    SetTextColor(hdc,TRANSLATE_COLOR(c_fgcol));
  end;
end;

/*___________________________________________________________________________*/


static char arg[10][30]={"","99","lorx","","","","","","",""};
static char *argv[10]={arg[0],arg[1],arg[2],arg[3],arg[4],arg[5],arg[6],arg[7],arg[8],arg[9]};
#pragma argsused

int PASCAL WinMain (HINSTANCE hI, HINSTANCE hPI,
     LPSTR lpszCmd, int nCS)
begin
  int i=0,j=1,k=0;

  /* decode the arguments in the call line */
  while (lpszCmd[k]!='\0')
  begin
    do {
      arg[j][i++]=lpszCmd[k++];
    while (! (lpszCmd[k]==SEPARATOR || lpszCmd[k]=='\0'));
    arg[j][i]='\0';
    argv[j]=arg[j];
    j++;i=0;
    while(lpszCmd[k]==SEPARATOR)k++;
  end;

  nCmdShow=nCS;
  hInstance=hI;hPrevInstance=hPI;
  mainEntry(j,argv);
  return 0;
end;

/*___________________________________________________________________________*/

long FAR PASCAL _export WndProc (HWND hwnd, WORD message, WORD wParam, LONG lParam)
{
  switch (message)
  {
   case WM_MOVE:
   case WM_PAINT:
    {
     HDC hdc;
     PAINTSTRUCT ps;

     hdc = BeginPaint( hwnd, &ps );
     restore_window_settings(hwnd,hdc);
     restore_window();
     SetBkMode( hdc, TRANSPARENT );
     EndPaint( hwnd, &ps );
    }
    break;
   case WM_SETFOCUS: restore_window_attributes();break;
    case WM_LBUTTONDOWN: ButtonState=1;break;
            case WM_LBUTTONUP  : ButtonState=0;break;

    case WM_DESTROY:
      PostQuitMessage (0) ;

      return 0 ;
    default: return (DefWindowProc (hwnd, message, wParam, lParam));
  }
   return NULL;

return (DefWindowProc (hwnd, message, wParam, lParam));
}


void set_pat()
begin
  int i,j;

  for (i=0;i<MAX_PATTERN_NO;i++)
  begin
    for(j=0;j<8;j++) *(patt_pntr[i]+j) = ~(*(patt_pntr[i]+j));
    hbmp_pat[i] = CreateBitmap(8, 8, 1, 1,  patt_pntr[i] );
  end;
end;

/*____________________________________________________________________________*/

void free_pat()
begin
  int i;

  for (i=0;i<MAX_PATTERN_NO;i++)
    DeleteObject( hbmp_pat[i] );
end;

/*____________________________________________________________________________*/

void OpenGraphics(hrs,vrs,bgcol,fgcol,ltx,lty)
int hrs,vrs,bgcol,fgcol,ltx,lty;

/* This is the internal implementation of the openGraphics function for Microsoft Windows */

begin
  static char szAppName[] = "MyClass" ;
//  MSG         msg ;
  WNDCLASS    wndclass ;
  HANDLE   hAccel;

//  HINSTANCE hinst = 0;
  long i;

  if (!hPrevInstance)
  {
    wndclass.style         = CS_HREDRAW | CS_VREDRAW ;
    wndclass.lpfnWndProc   = (WNDPROC)WndProc ;
    wndclass.cbClsExtra    = 0 ;
    wndclass.cbWndExtra    = 0 ;
    wndclass.hInstance     = hInstance ;
    wndclass.hIcon         = LoadIcon( NULL, IDI_APPLICATION );
    wndclass.hCursor       = LoadCursor (NULL, IDC_ARROW) ;
    wndclass.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    wndclass.lpszMenuName  = MAKEINTRESOURCE(2);
    wndclass.lpszClassName = szAppName ;

    RegisterClass (&wndclass) ;
 }


hwnd = CreateWindow("MyClass", "KRAK", WS_OVERLAPPEDWINDOW,
//hwnd = CreateWindow("MyClass", NULL, WS_BORDER,
    0,      /* horizontal position */
    0,                      /* vertical position   */
    hrs,                 /* width               */
    vrs+33,              /* height              */

    (HWND) NULL, (HMENU) NULL, hInstance, (LPSTR) NULL);

  ShowWindow (hwnd, nCmdShow) ;
  UpdateWindow (hwnd) ;
  hAccel = LoadAccelerators( hInstance,
   MAKEINTRESOURCE(3) );

  hdc = GetDC(hwnd);
  ijoff=GetDCOrg(hdc);
  ioff=LOWORD(ijoff); joff=HIWORD(ijoff);
  SetCursorPos(0,0);
  SetMapMode(hdc, MM_TEXT);

  lb.lbStyle = BS_NULL;
  lb.lbHatch = HS_BDIAGONAL;
  nullhbr = CreateBrushIndirect(&lb);

  plf = (PLOGFONT) farmalloc(sizeof(LOGFONT)); /*LocalAlloc(LPTR, sizeof(LOGFONT));*/
  for(i=0;i<sizeof(LOGFONT);i++) *((char *)plf+i)=0;
  plf->lfHeight = -MulDiv(8,GetDeviceCaps(hdc,LOGPIXELSY),72);
  /*plf->lfFaceName[0]='\0'; */
  strcpy(plf->lfFaceName,"");
  plf->lfPitchAndFamily=FIXED_PITCH+FF_MODERN;

  hfont = CreateFontIndirect(plf);
  hfontOld = SelectObject(hdc, hfont);
  farfree(plf);

/* set_col();*/
  set_colors();  /* nie przetestowana zmiana - set_colors w color_ha.c */
# ifdef BLACKWHITE
# else
// The first, commented out, version does not work - it was suppoed
// to leave the first 20 colors from the system palette untouched.
/*  plgpl = (LOGPALETTE*) farmalloc(
    sizeof(LOGPALETTE) + (20+MAX_PALETTE) * sizeof(PALETTEENTRY));

  plgpl->palNumEntries = 20+MAX_PALETTE;
  plgpl->palVersion = 0x300;

/*nie przetestowane zmiany - patrz wyzej */
  GetSystemPaletteEntries(hdc,0,20,plgpl->palPalEntry);

  for (i = 20; i < 20+MAX_PALETTE;i++)
  begin
    plgpl->palPalEntry[i].peRed = (BYTE)(255*red_c[i]);
    plgpl->palPalEntry[i].peGreen = (BYTE)(255*green_c[i]);
    plgpl->palPalEntry[i].peBlue = (BYTE)(255*blue_c[i]);
    plgpl->palPalEntry[i].peFlags = PC_RESERVED;
  end;
  hpal = CreatePalette(plgpl);
  farfree(plgpl);

  hPalPrevious = SelectPalette(hdc, hpal, FALSE);
  use_palette=1;
  if ((ncol=RealizePalette(hdc)) == NULL) use_palette=0;
*/
  plgpl = (LOGPALETTE*) farmalloc(
    sizeof(LOGPALETTE) + MAX_PALETTE * sizeof(PALETTEENTRY));

  plgpl->palNumEntries = MAX_PALETTE;
  plgpl->palVersion = 0x300;

/*nie przetestowane zmiany - patrz wyzej */
  for (i = 0; i < MAX_PALETTE;i++)
  begin
    plgpl->palPalEntry[i].peRed = (BYTE)(255*red_c[i]);
    plgpl->palPalEntry[i].peGreen = (BYTE)(255*green_c[i]);
    plgpl->palPalEntry[i].peBlue = (BYTE)(255*blue_c[i]);
    plgpl->palPalEntry[i].peFlags = PC_RESERVED;
  end;
  hpal = CreatePalette(plgpl);
  farfree(plgpl);

  hPalPrevious = SelectPalette(hdc, hpal, FALSE);
  use_palette=1;
  if ((ncol=RealizePalette(hdc)) == NULL) use_palette=0;

# endif
  SetBkColor(hdc,TRANSLATE_COLOR(bgcol));
  c_bgcol=bgcol;
  SetTextColor(hdc,TRANSLATE_COLOR(fgcol));
  c_fgcol=fgcol;

  set_pat();
end;

/*___________________________________________________________________________*/

void CloseGraphics()

/* This is the internal implementation of the closeGraphics function for Microsoft Windows.
*/

begin
  DeleteObject(hpal);
  free_pat();
  ReleaseDC(hwnd, hdc);
  DestroyWindow(hwnd);
end;

/*____________________________________________________________________________*/

void SetBgCol(col)
INT col;
/* SetBgCol changes the background color to col */
begin
    SetBkColor(hdc,TRANSLATE_COLOR(col));
    c_bgcol=col;
end;

/*____________________________________________________________________________*/

void SetFgCol(col)
INT col;
/* SetFgCol changes the foreground color to col */
begin
    SetTextColor(hdc,TRANSLATE_COLOR(col));
    c_fgcol=col;
end;

/*___________________________________________________________________________*/

void MoveTo(INT i,INT j)
begin
  MoveTo(hdc,i,j);
end;
/*___________________________________________________________________________*/

#undef LineTo

void MWLineTo(i,j)
INT i,j;
/* This is the implementation of the LineTo function
   redefined by a macro to MWLineTo to avoid collision
   with the LineTo function in the Windows package
*/

begin
  HPEN hpen, hpenOld;

  hpen = CreatePen(PS_SOLID, 1, TRANSLATE_COLOR(c_fgcol));
  hpenOld = SelectObject(hdc, hpen);

  LineTo(hdc,i,j);
  SelectObject(hdc, hpenOld);
  DeleteObject(hpen);
end;
/*___________________________________________________________________________*/

void PlotDot(i,j)
INT i,j;

/*  This is the internal implementation of the plotDot function for Microsoft Windows.     */

begin
  SetPixel(hdc,i,j,TRANSLATE_COLOR(c_fgcol));
end;

/*___________________________________________________________________________*/


void Crcl(i,j,r)
INT i,j,r;
begin
  HPEN hpen, hpenOld;

  hpen = CreatePen(PS_SOLID, 1, TRANSLATE_COLOR(c_fgcol));
  hpenOld = SelectObject(hdc, hpen);

  Ellipse(hdc,i-r,j-r,i+r,j+r);

  SelectObject(hdc, hpenOld);
  DeleteObject(hpen);

end;

/*___________________________________________________________________________*/

void DrawStrng(txt)
const char *txt;

begin
  POINT pt;

  GetCurrentPositionEx(hdc,&pt);
  TextOut(hdc,pt.x,pt.y,txt,strlen(txt));
end;

/*___________________________________________________________________________*/

 void FillRct(r,pattNr,colNr)
 RCT * r;
 int pattNr,colNr;

 begin
   HBRUSH hbr,hbrOld;
   RCT r_inv;

   r_inv.lti=r->ltj;
   r_inv.rbi=r->rbj;
   r_inv.ltj=r->lti;
   r_inv.rbj=r->rbi;

   hbr = CreatePatternBrush(hbmp_pat[pattNr]);
   hbrOld = SelectObject(hdc, hbr);
   SetTextColor(hdc,TRANSLATE_COLOR(colNr));

   FillRect(hdc,(const RECT FAR *)&r_inv,hbr);

   SelectObject(hdc,hbrOld);
   DeleteObject(hbr);
   SetTextColor(hdc,TRANSLATE_COLOR(c_fgcol));
 end;

/*___________________________________________________________________________*/

void GetMouse(pxl)
PXL *pxl;

begin
  POINT pt;
  RECT rc;

//  EmptyMQueue();
  GetClientRect(hwnd,&rc);
  GetCursorPos(&pt);
//gprintf_at(rootFrm,15,10,"%d  %d",rc.right,rc.bottom);
  pxl->i=std::min(pt.x-ioff,rc.right-1);
  pxl->j=std::min(pt.y-joff,rc.bottom-1);
end;
/*___________________________________________________________________________*/

int Button()
begin
  POINT pt;
  RECT rc;

//  EmptyMQueue();
  GetClientRect(hwnd,&rc);
  GetCursorPos(&pt);
//  DrawStrng("ButtonState");

  if(hwnd==GetFocus() && (pt.x-ioff<=rc.right-1) && (pt.y<=joff,rc.bottom-1) && (pt.x>=0) && (pt.y>=0))
  {
    return (GetAsyncKeyState(VK_LBUTTON)>=0x8000?1:0);
  } else {
    return 0;
  }
//  return 0;
end;

/*___________________________________________________________________________*/

static long tick=0,last_tick=0;

long tickClock()
begin
  long new_tick;

  new_tick=clock();
  tick+=new_tick-last_tick;
  last_tick=new_tick;
  return tick;
end;

/*___________________________________________________________________________*/

/*
DREAL Clock(void)
/* Function iClock returns process time in seconds as a double */
begin
  return (DREAL)tickClock()/CLK_TCK;
end;
*/

/*___________________________________________________________________________*/
/*
DREAL Clock(void)
/* Function iClock returns process time in seconds as a double */
begin
  return (DREAL)time(NULL);
end;
*/

DREAL Clock(void)
/* Function iClock returns process time in seconds as a double */
begin
  struct time t;
  gettime(&t);
  return ((DREAL)t.ti_hund)/100.0+t.ti_sec+60*(t.ti_min+60*t.ti_hour);
end;


/*___________________________________________________________________________*/

DREAL tck2sec(long tck)
begin
  return (DREAL)tck/CLK_TCK;
end;

/*___________________________________________________________________________*/

void Beep(freq,time)
INT freq,time;
begin
end;

/*___________________________________________________________________________*/

char *datetime()
begin
  time_t t;

  time(&t);
  return (ctime(&t));
end;

/*___________________________________________________________________________*/

int GetKey()
begin
  MSG msg;
  int key=NO_KEY,key1=NO_KEY,key2=NO_KEY;

  while (PeekMessage(&msg, NULL, 0, 0, PM_REMOVE))
  begin
    if(msg.message == WM_KEYDOWN) key1 = msg.wParam;
    if(msg.message == WM_CHAR) key2 = msg.wParam;
//    if(msg.message == WM_SYSKEYDOWN) key1 = msg.wParam;
//    if(msg.message == WM_CHAR) key2 = *((char *)(&(msg.lParam))+2);
    if(msg.message == WM_QUIT) exit(0);
    TranslateMessage(&msg);
    DispatchMessage(&msg);
  end;

  if(key1>=16 && key1<=18) key1=NO_KEY;// disregard SHIFTs as keys
  if(key1!=NO_KEY)
  begin
    key1-=19;
    if(key1>=26) key1-=4;
  end;

  return ( key2!=NO_KEY ? key2 : key1);
//  return key1;
end;

/*begin
  int ch;


  if (kbhit()!=0) ch= (int)getch();
  else ch=NO_KEY;

  return ch;
end;*/



/*___________________________________________________________________________*/

/// @}
