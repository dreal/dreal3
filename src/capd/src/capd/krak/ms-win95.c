/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ms-win95.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#undef LineTo

#include <windows.h>
#include <conio.h>
#include <dos.h>
#include <iostream>

#ifdef NO_CMD_LINE_ARGS
int mainEntry(void);
#else
int mainEntry(int argc, char *argv[]);
#endif

void EmptyMQueue(void);
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
#endif
#define SEPARATOR ';'
//int use_palette=1;
int use_palette;
namespace capd{
namespace krak{
   class Frame;
   extern capd::krak::Frame *cFrm,*rootFrm;
   extern int fontWdth,fontHght;
   extern int what_restore;
   int c_bgcol,c_fgcol;
   extern void (*restore_window)(void);
   extern float red_c[MAX_PALETTE],green_c[MAX_PALETTE],blue_c[MAX_PALETTE];
}}

#ifdef _REFRESH_
HBITMAP mapa;
HDC kontMapy;
int Width, Height;
#endif

char emptytext[]="";

int nCmdShow;
HDC  hdc;
WORD ioff,joff,ncol;
DWORD ijoff;
POINT off;
HWND hwnd ;
HINSTANCE hInstance,hPrevInstance;

LOGBRUSH lb;
HBRUSH nullhbr, hbrOld;

HPALETTE hpal=NULL,hPalPrevious;
LOGPALETTE *plgpl;

HGDIOBJ hfont, hfontOld;
PLOGFONT plf;

HBITMAP hbmp_pat[MAX_PATTERN_NO];

static int ButtonState=0;


/*___________________________________________________________________________*/

void EmptyMQueue()
{
   MSG msg;

   while (PeekMessage(&msg, NULL, 0, 0, PM_REMOVE))
   {
      if(msg.message == WM_QUIT) exit(0);
      TranslateMessage(&msg);
      DispatchMessage(&msg);
   }
}

/*___________________________________________________________________________*/

namespace capd{
namespace krak{
void restore_window_settings(HWND hwnd,HDC hdc)
{
   POINT p;
// BOOL b;
   LPPOINT lp=&p;
// b=GetDCOrgEx(hdc,lp);
   GetDCOrgEx(hdc,lp);
   ioff=p.x; joff=p.y;
}

void restore_window_attributes(HWND hwnd,HDC hdc)
{
   SetMapMode(hdc, MM_TEXT);

   hfontOld = SelectObject(hdc, hfont);

   if(hpal!=NULL)
   {
      hPalPrevious = SelectPalette(hdc, hpal, FALSE);
      //  if ((ncol=RealizePalette(hdc)) == GDI_ERROR);
      ncol=RealizePalette(hdc);

      //  MessageBox(hwnd, "Can't realize palette", "Error", MB_OK);

      SetBkColor(hdc,TRANSLATE_COLOR(capd::krak::c_bgcol));
      SetTextColor(hdc,TRANSLATE_COLOR(capd::krak::c_fgcol));
   }
}
}} // the end of the namespace capd::krak
/*___________________________________________________________________________*/


static char arg[10][30]={"","99","lorx","","","","","","",""};
static char *argv[10]={arg[0],arg[1],arg[2],arg[3],arg[4],arg[5],arg[6],arg[7],arg[8],arg[9]};
//#pragma argsused

int PASCAL WinMain (HINSTANCE hI, HINSTANCE hPI, LPSTR lpszCmd, int nCS)
{
   int i=0,j=1,k=0;

#ifdef NO_CMD_LINE_ARGS
   nCmdShow=nCS;
   hInstance=hI;hPrevInstance=hPI;
   mainEntry();
#else
  /* decode the arguments in the call line */
   while (lpszCmd[k]!='\0')
   {
      do {
         arg[j][i++]=lpszCmd[k++];
      } while(!(lpszCmd[k]==SEPARATOR || lpszCmd[k]=='\0'));
      arg[j][i]='\0';
      argv[j]=arg[j];
      j++; i=0;
      while(lpszCmd[k]==SEPARATOR) k++;
   }

   nCmdShow=nCS;
   hInstance=hI;hPrevInstance=hPI;
   mainEntry(j,argv);
#endif
   return 0;
}

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
         capd::krak::restore_window_settings(hwnd,hdc);
#ifdef _REFRESH_
         BitBlt(hdc, 0, 0, Width, Height, kontMapy, 0, 0, SRCCOPY);
#else
         capd::krak::restore_window();
#endif
         SetBkMode( hdc, TRANSPARENT );
         EndPaint( hwnd, &ps );
      }
      break;
//    case WM_SETFOCUS: restore_window_attributes(hwnd,hwc);break;
      case WM_SETFOCUS: break;
      case WM_LBUTTONDOWN: ButtonState=1;break;
      case WM_LBUTTONUP  : ButtonState=0;break;

      case WM_DESTROY:
         PostQuitMessage (0) ;
         return 0 ;
      default: return (DefWindowProc (hwnd, message, wParam, lParam));
   }

   return (DefWindowProc (hwnd, message, wParam, lParam));
}


void set_pat()
{
   int i,j;

   for (i=0;i<MAX_PATTERN_NO;i++)
   {
      for(j=0;j<8;j++)
         *(capd::krak::patt_pntr[i]+j) = ~(*(capd::krak::patt_pntr[i]+j));
      hbmp_pat[i] = CreateBitmap(8, 8, 1, 1,  NULL);
      SetBitmapBits(hbmp_pat[i],8,capd::krak::patt_pntr[i]);
   }
}

/*____________________________________________________________________________*/

void free_pat()
{
   int i;

   for (i=0;i<MAX_PATTERN_NO;i++)
      DeleteObject( hbmp_pat[i] );
}

/*____________________________________________________________________________*/
namespace capd{
namespace krak{

// the font size that is currently in use
static int fontSize = 10;

void SetTextSize(int size)
/* SetTextSize changes the text size to size points */
{
    fontSize = size;
//  plf = (PLOGFONT) farmalloc(sizeof(LOGFONT)); /*LocalAlloc(LPTR, sizeof(LOGFONT));*/
   plf = (PLOGFONT) new LOGFONT; /*LocalAlloc(LPTR, sizeof(LOGFONT));*/
   for(unsigned long i=0;i<sizeof(LOGFONT);i++)
      *((char *)plf+i)=0;
   plf->lfHeight = -MulDiv(size,GetDeviceCaps(hdc,LOGPIXELSY),72);
   strcpy(plf->lfFaceName,"");
   plf->lfPitchAndFamily=FIXED_PITCH+FF_MODERN;

   hfont = CreateFontIndirect(plf);
   hfontOld = SelectObject(hdc, hfont);
#ifdef _REFRESH_
   SelectObject(kontMapy, hfont);
#endif
//  farfree(plf);
   delete plf;
   SIZE  s;
   GetTextExtentPoint32(hdc,"X",1,&s);
   capd::krak::fontHght=s.cy;
   capd::krak::fontWdth=s.cx;
}

int GetTextSize (void)
{
   return fontSize;
}

/*____________________________________________________________________________*/

//void OpenGraphics(int hrs,int vrs,int bgcol,int fgcol)
void OpenGraphics(int hrs,int vrs,int bgcol,int fgcol,int ltx,int lty)
/* This is the internal implementation of the openGraphics function for Microsoft Windows */
{
   static char szAppName[] = "MyClass" ;
   WNDCLASS    wndclass ;

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
   ltx,                 /* horizontal position */
   lty,                 /* vertical position   */
   hrs,                 /* width               */
   vrs,                 /* height              */
//    Extra 33 was used to correct the window for some compilers
//    Who knows which one?
//    vrs+33,              /* height              */

   (HWND) NULL, (HMENU) NULL, hInstance, (LPSTR) NULL);
   hdc = GetDC(hwnd);
#ifdef _REFRESH_
   Width = hrs;
   Height = vrs;
   mapa = CreateCompatibleBitmap(hdc, Width, Height);
// Create a context for a bitmap
   kontMapy = CreateCompatibleDC(hdc);
// Choose a map for created context
   SelectObject(kontMapy, mapa);
// Fill the bitmap with white brush
   SetBkColor(kontMapy,TRANSLATE_COLOR(bgcol));
   SetTextColor(kontMapy,TRANSLATE_COLOR(fgcol));
   PatBlt(kontMapy, 0, 0, Width, Height, WHITENESS);
   SetMapMode(kontMapy, MM_TEXT);

#endif

   ShowWindow (hwnd, nCmdShow) ;
   UpdateWindow (hwnd) ;
// hAccel = LoadAccelerators( hInstance,
// MAKEINTRESOURCE(3) );


   POINT p;
   GetDCOrgEx(hdc,&p);
   SetMapMode(hdc, MM_TEXT);
   capd::krak::SetTextSize(8);
   ioff=p.x; joff=p.y;
//  SetCursorPos(0,0);
   lb.lbStyle = BS_NULL;
   lb.lbHatch = HS_BDIAGONAL;
   nullhbr = CreateBrushIndirect(&lb);

   capd::krak::set_colors();

//  plgpl = (LOGPALETTE*) farmalloc(
   plgpl = (LOGPALETTE*) malloc(sizeof(LOGPALETTE) + MAX_PALETTE * sizeof(PALETTEENTRY));

   plgpl->palNumEntries = MAX_PALETTE;
   plgpl->palVersion = 0x300;

   for (i = 0; i < MAX_PALETTE;i++)
   {
      plgpl->palPalEntry[i].peRed = (BYTE)(255*capd::krak::red_c[i]);
      plgpl->palPalEntry[i].peGreen = (BYTE)(255*capd::krak::green_c[i]);
      plgpl->palPalEntry[i].peBlue = (BYTE)(255*capd::krak::blue_c[i]);
      plgpl->palPalEntry[i].peFlags = PC_RESERVED;
   }
   hpal = CreatePalette(plgpl);
   free(plgpl);

   hPalPrevious = SelectPalette(hdc, hpal, FALSE);
#ifdef _REFRESH_
   SelectPalette(kontMapy, hpal, FALSE);
#endif
   use_palette=1;
   UINT n=RealizePalette(hdc);
   ncol=(WORD)(n);
   if (n == GDI_ERROR) use_palette=0;
   SetBkColor(hdc,TRANSLATE_COLOR(bgcol));
   capd::krak::c_bgcol=bgcol;
   SetTextColor(hdc,TRANSLATE_COLOR(fgcol));
   c_fgcol=fgcol;

   set_pat();
}

/*___________________________________________________________________________*/

void CloseGraphics()

/* This is the internal implementation of the closeGraphics function for Microsoft Windows.
*/

{
#ifdef _REFRESH_
   DeleteDC(kontMapy);
   DeleteObject(mapa);
#endif
   DeleteObject(hpal);
   free_pat();
   ReleaseDC(hwnd, hdc);
   DestroyWindow(hwnd);
}

/*____________________________________________________________________________*/

void SetBgCol(int col)
/* SetBgCol changes the background color to col */
{
   SetBkColor(hdc,TRANSLATE_COLOR(col));
   capd::krak::c_bgcol=col;
#ifdef _REFRESH_
   SetBkColor(kontMapy,TRANSLATE_COLOR(col));
#endif
}

/*____________________________________________________________________________*/

void SetFgCol(int col)
/* SetFgCol changes the foreground color to col */
{
   SetTextColor(hdc,TRANSLATE_COLOR(col));
   capd::krak::c_fgcol=col;
#ifdef _REFRESH_
   SetTextColor(kontMapy,TRANSLATE_COLOR(col));
#endif
}

/*___________________________________________________________________________*/

/* MoveTo(i,j);  is implemented as a macro */

/*___________________________________________________________________________*/

void MoveTo(int i,int j)
{
   MoveToEx(hdc,i,j,NULL);
#ifdef _REFRESH_
   MoveToEx(kontMapy,i,j,NULL);
#endif
}


void MWLineTo(int i,int j)
/* This is the implementation of the LineTo function
   redefined by a macro to MWLineTo to avoid collision
   with the LineTo function in the Windows package
*/
{
   HGDIOBJ hpen, hpenOld;
   hpen = CreatePen(PS_SOLID, 1, TRANSLATE_COLOR(c_fgcol));
   hpenOld = SelectObject(hdc, hpen);

   LineTo(hdc,i,j);

   SelectObject(hdc, hpenOld);
   DeleteObject(hpen);
#ifdef _REFRESH_
   hpen = CreatePen(PS_SOLID, 1, TRANSLATE_COLOR(capd::krak::c_fgcol));
   hpenOld = SelectObject(kontMapy, hpen);
   LineTo(kontMapy,i,j);
   SelectObject(kontMapy, hpenOld);
   DeleteObject(hpen);
#endif
}
/*___________________________________________________________________________*/

void PlotDot(int i,int j)
/*  This is the internal implementation of the plotDot function for Microsoft Windows.     */
{
   SetPixel(hdc,i,j,TRANSLATE_COLOR(capd::krak::c_fgcol));
#ifdef _REFRESH_
   SetPixel(kontMapy,i,j,TRANSLATE_COLOR(capd::krak::c_fgcol));
#endif
}

/*___________________________________________________________________________*/


void Crcl(int i,int j,int r)
{
   HGDIOBJ hpen, hpenOld;

   hpen = CreatePen(PS_SOLID, 1, TRANSLATE_COLOR(capd::krak::c_fgcol));
   hpenOld = SelectObject(hdc, hpen);

   Ellipse(hdc,i-r,j-r,i+r,j+r);

   SelectObject(hdc, hpenOld);
   DeleteObject(hpen);
#ifdef _REFRESH_
   hpen = CreatePen(PS_SOLID, 1, TRANSLATE_COLOR(capd::krak::c_fgcol));
   hpenOld = SelectObject(kontMapy, hpen);
   Ellipse(kontMapy,i-r,j-r,i+r,j+r);
   SelectObject(kontMapy, hpenOld);
   DeleteObject(hpen);
#endif
}

/*___________________________________________________________________________*/

void DrawStrng(const char *txt)
{
   POINT pt;

   GetCurrentPositionEx(hdc,&pt);
   TextOut(hdc,pt.x,pt.y,txt,strlen(txt));
#ifdef _REFRESH_
   TextOut(kontMapy,pt.x,pt.y,txt,strlen(txt));
#endif
}

/*___________________________________________________________________________*/

void FillRct(capd::krak::Rct *r,int pattNr,int colNr)
{
   HGDIOBJ hbrOld;
   HBRUSH hbr;
   RECT r_inv;

   r_inv.top=r->ltj;
   r_inv.bottom=r->rbj;
   r_inv.left=r->lti;
   r_inv.right=r->rbi;

   hbr = CreatePatternBrush(hbmp_pat[pattNr]);
   hbrOld = SelectObject(hdc, hbr);
   SetTextColor(hdc,TRANSLATE_COLOR(colNr));

   FillRect(hdc,&r_inv,hbr);

   SelectObject(hdc,hbrOld);
   DeleteObject(hbr);
   SetTextColor(hdc,TRANSLATE_COLOR(capd::krak::c_fgcol));
#ifdef _REFRESH_
   hbr = CreatePatternBrush(hbmp_pat[pattNr]);
   hbrOld = SelectObject(kontMapy, hbr);
   SetTextColor(kontMapy,TRANSLATE_COLOR(colNr));
   FillRect(kontMapy,&r_inv,hbr);
   SelectObject(kontMapy,hbrOld);
   DeleteObject(hbr);
   SetTextColor(kontMapy,TRANSLATE_COLOR(capd::krak::c_fgcol));
#endif
}

/*___________________________________________________________________________*/

void FillChord(int ltj, int lti, int rbj, int rbi, int bj, int bi, int ej, int ei, int pattNr, int colNr)
{
   HGDIOBJ hbrOld;
   HBRUSH hbr;

   hbr = CreatePatternBrush(hbmp_pat[pattNr]);
   hbrOld = SelectObject(hdc, hbr);
   SetTextColor(hdc,TRANSLATE_COLOR(colNr));

   Chord(hdc,ltj,lti,rbj,rbi,bj,bi,ej,ei);

   SelectObject(hdc,hbrOld);
   DeleteObject(hbr);
   SetTextColor(hdc,TRANSLATE_COLOR(capd::krak::c_fgcol));
#ifdef _REFRESH_
   hbr = CreatePatternBrush(hbmp_pat[pattNr]);
   hbrOld = SelectObject(kontMapy, hbr);
   SetTextColor(kontMapy,TRANSLATE_COLOR(colNr));
   Chord(kontMapy,ltj,lti,rbj,rbi,bj,bi,ej,ei);
   SelectObject(kontMapy,hbrOld);
   DeleteObject(hbr);
   SetTextColor(kontMapy,TRANSLATE_COLOR(capd::krak::c_fgcol));
#endif
}

/*___________________________________________________________________________*/

void Arc(int ltj, int lti, int rbj, int rbi, int bj, int bi, int ej, int ei, int colNr)
{
   HGDIOBJ hpen, hpenOld;
   hpen = CreatePen(PS_SOLID, 1, TRANSLATE_COLOR(colNr));
   hpenOld = SelectObject(hdc, hpen);

   ::Arc(hdc,ltj,lti,rbj,rbi,bj,bi,ej,ei);

   SelectObject(hdc, hpenOld);
#ifdef _REFRESH_
   hpenOld = SelectObject(kontMapy, hpen);
   ::Arc(kontMapy,ltj,lti,rbj,rbi,bj,bi,ej,ei);
   SelectObject(kontMapy,hpenOld);
#endif
   DeleteObject(hpen);
}

/*___________________________________________________________________________*/

void FillRgn(int *r, int lPoints, int pattNr, int colNr)
{
   HGDIOBJ hbrOld;
   HBRUSH hbr;
   POINT *pt = (POINT *)malloc(lPoints*sizeof(POINT));
   int i;
   for(i=0;i<lPoints;i++)
   {
      (*(pt+i)).x=r[i+i];
      (*(pt+i)).y=r[i+i+1];
   }
   HRGN hrgn=CreatePolygonRgn(pt,lPoints,ALTERNATE);

   hbr = CreatePatternBrush(hbmp_pat[pattNr]);
   hbrOld = SelectObject(hdc, hbr);
//   For some reason the the call below is not performed under Dev-C++ 5 beta
//   SetTextColor(hdc,TRANSLATE_COLOR(colNr));
   SetFgCol(colNr);
   ::FillRgn(hdc,hrgn,hbr);

   SelectObject(hdc,hbrOld);
   SetTextColor(hdc,TRANSLATE_COLOR(capd::krak::c_fgcol));

#ifdef _REFRESH_
   hbrOld = SelectObject(kontMapy, hbr);
   SetTextColor(kontMapy,TRANSLATE_COLOR(colNr));
   ::FillRgn(hdc,hrgn,hbr);
   SelectObject(kontMapy,hbrOld);
   SetTextColor(kontMapy,TRANSLATE_COLOR(capd::krak::c_fgcol));
#endif

   DeleteObject(hrgn);
   DeleteObject(hbr);
   free(pt);
}

/*___________________________________________________________________________*/

void GetMouse(capd::krak::Pxl *pxl)
{
   POINT pt;
   RECT rc;

   GetClientRect(hwnd,&rc);
   GetCursorPos(&pt);
   pxl->i=std::min(pt.x-ioff,rc.right-1);
   pxl->j=std::min(pt.y-joff,rc.bottom-1);
}
/*___________________________________________________________________________*/

int Button()
{
   POINT pt;
   RECT rc;

   GetClientRect(hwnd,&rc);
   GetCursorPos(&pt);

// if(hwnd==GetFocus() && (pt.x-ioff<=rc.right-1) && (pt.y<=joff,rc.bottom-1) && (pt.x>=0) && (pt.y>=0))
// Powy�ej by� oc najmniej jeden b��d (pt.y<=joff,rc.bottom-1), a dla Borlanda chyba trzeba odejmowa� ioff i joff wsz�dzie
   if(hwnd==GetFocus() && (pt.x-ioff<=rc.right-1) && (pt.y-joff<=rc.bottom-1) && (pt.x-ioff>=0) && (pt.y-joff>=0))
   {
      return (GetAsyncKeyState(VK_LBUTTON) & 0x8000 ? 1 : 0 );
   } else {
      return 0;
   }
}

/*___________________________________________________________________________*/

static long tick=0,last_tick=0;

long tickClock()
{
   long new_tick;

   new_tick=clock();
   tick+=new_tick-last_tick;
   last_tick=new_tick;
   return tick;
}

/*___________________________________________________________________________*/

double Clock(void)
/* Function iClock returns process time in seconds as a double */
{
   return (double)tickClock()/CLK_TCK;
}

/*___________________________________________________________________________*/

/*___________________________________________________________________________*/

double tck2sec(long tck)
{
   return (double)tck/CLK_TCK;
}

/*___________________________________________________________________________*/

void Beep(int freq,int time)
{}

/*___________________________________________________________________________*/

char *datetime()
{
   time_t t;

   time(&t);
   return (ctime(&t));
}

/*___________________________________________________________________________*/

int GetKey()
{
   MSG msg;
// int key=NO_KEY,key1=NO_KEY,key2=NO_KEY;
   int key1=NO_KEY,key2=NO_KEY;

   while (PeekMessage(&msg, NULL, 0, 0, PM_REMOVE))
   {
      if(msg.message == WM_KEYDOWN) key1 = msg.wParam;
      if(msg.message == WM_CHAR) key2 = msg.wParam;
      if(msg.message == WM_QUIT) exit(0);
      TranslateMessage(&msg);
      DispatchMessage(&msg);
   }

   if(key1>=16 && key1<=18) key1=NO_KEY;// disregard SHIFTs as keys
   if(key1!=NO_KEY)
   {
      key1-=19;
      if(key1>=26) key1-=4;
   }

   return ( key2!=NO_KEY ? key2 : key1);
}


/*___________________________________________________________________________*/

}} // the end of the namespace capd::krak

/// @}
