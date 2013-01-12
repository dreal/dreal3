/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file sun.c
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include <stdio.h>

//#include "poinc_de.h"  // This is an old file and shouldn't be needed here

//#include "capd/capd/myC.h"

#include <sys/ioctl.h>

#include <sys/file.h>

#include <sys/types.h>

#include <sys/time.h>
#include <sys/times.h>

#include "Xlib.h"
#include </usr/openwin/include/X11/Xutil.h>
#include </usr/openwin/include/X11/Xos.h>

#define SC(c,r,g,b) red_a[c]=r;green_a[c]=g;blue_a[c]=b;

extern INT fontWdth,fontHght;
extern INT isgraphic;
extern float red_c[],green_c[],blue_c[];

int top_marg_size=0; // depends on a particular implmentation of XWin

/* specific Xwindows variables */

static char *colorname[] =
{
  "white","black","red","green",
  "blue","yellow","magenta","cyan",
  "orange","violet","dark green","brown",
  "khaki","dark slate blue","orange red","sea green"
};

XColor exact_defs[/*MAX_COLOR_NO*/MAX_PALETTE];
Pixmap stipple[30];
GC drawgc;
unsigned long fg_pixel, bg_pixel; /* index into colormap */
unsigned long valuemask = 0; /* ignore XGCvalues and use defaults */
XGCValues values;
Window win;
unsigned int WX = 0, WY = 0;     /* window position */
unsigned int border_width = 4;  /* four pixels */
XSizeHints size_hints;
XEvent report;
XFontStruct *font_info;

char *display_name = NULL;
Region region;          /* for exposure event processing */
XRectangle rectangle;   /* for exposure event processing */

Display *display;
int screen;

char *fontname = "9x15";

int default_depth;
Colormap default_cmap;
long unsigned int plane_masks[1];
XVisualInfo visual_info;
int Class;
long unsigned int colors[/*MAX_COLOR_NO*/MAX_PALETTE];

int color_no;
int c_ipstn=0,c_jpstn=0,c_bgcol,c_fgcol;

long event_mask= ExposureMask | KeyPressMask | ButtonPressMask |
                 ButtonReleaseMask | ButtonMotionMask | PointerMotionHintMask |
                 StructureNotifyMask;



/*____________________________________________________________________________*/

void opengfxwndw(int wn, int hsr, int vsr, int bgcolor, int fgcolor, int argc, char **argv)

/* This function opens window in XWINDOWS for graphics. */

{

unsigned int line_width = 1;
int line_style = LineSolid;
int cap_style = CapButt;
int join_style = JoinRound;
int dash_offset = 0;
static char dash_list[] = {12, 24};
int i;

/*----------------------- connect to X server --------------------------------*/

  if( (display=XOpenDisplay(display_name)) == NULL )
  {
    fprintf( stderr,"cannot connect to X server %s\n",
      XDisplayName(display_name));
    exit( -1 );
  }

  XSynchronize(display,True);
  screen = DefaultScreen(display);

/*--------size window with enough room for text (screen 1172x900) -----------*/

  /*getcolors*/

  default_depth = DefaultDepth(display, screen);
  default_cmap   = DefaultColormap(display, screen);

/*  printf("Available %d display cells\n"
                         ,DisplayCells(display,DefaultScreen(display))); */

  if(!XMatchVisualInfo(display,screen,default_depth,PseudoColor,&visual_info))
  {
    fprintf(stderr,"Not a pseudocolor type screen\n");
    exit(0);
  }

/*------------- allocate as many cells as we can ----------------------------*/

//  color_no = MAX_COLOR_NO;
  color_no = MAX_PALETTE;
  set_colors();

  for(;;){
    if(XAllocColorCells(display,default_cmap,
                        False,plane_masks,0,colors,color_no)) break;
    color_no--;
    if( color_no = 0)
    {

      /* can't allocate 16 colors, use black and white */
      fprintf(stderr,"Can't allocate color cells\n");
      exit(0);
    }
  }
  for (i = 0; i < color_no; i++)
  {
    /* set pixel value in struct to the allocated one */
    exact_defs[i].pixel = colors[i];

    if (i<MAX_COLOR_NO)
    {
      if( !XParseColor(display, default_cmap, colorname[i], &exact_defs[i]))
      fprintf(stderr,"color name %s not in database", colorname[i]);
    } else {
      exact_defs[i].red   = (short)(65535*red_c[i]);
      exact_defs[i].green = (short)(65535*green_c[i]);
      exact_defs[i].blue  = (short)(65535*blue_c[i]);
    }
    /* this needed before calling XStoreColors */
    exact_defs[i].flags = DoRed | DoGreen | DoBlue;
  }

  /* this sets the color of read/write cell */
  XStoreColors(display, default_cmap, exact_defs, color_no);

/*  printf("Allocated %d colors\n",color_no); */

  bg_pixel = exact_defs[bgcolor].pixel;
  fg_pixel = exact_defs[fgcolor].pixel;

/*------------------------- create opaque window ----------------------------*/

  win = XCreateSimpleWindow(display, RootWindow(display,screen), WX, WY,
            hsr, vsr+top_marg_size, border_width,fg_pixel,bg_pixel);

/*--------------------------- Set resize hints ------------------------------*/

  size_hints.flags = PPosition | PSize | PMinSize;
  size_hints.x = WX;
  size_hints.y = WY;
  size_hints.width = hsr;
  size_hints.height = vsr;
  size_hints.min_width = 300;
  size_hints.min_height = 200;

/* --------set Properties for window manager (always before mapping) --------*/

  XSetStandardProperties(display, win, argv[0],argv[0],NULL,
                         argv, argc, &size_hints);

/*-------------------------- Select event types wanted ----------------------*/

  XSelectInput(display, win, event_mask);

/*----------------------------- Access font -------------------------------- */

  if ((font_info = XLoadQueryFont(display,fontname)) == NULL)
  {
    fprintf( stderr, "Basic: Cannot open 9x15 font\n");
    exit( -1 );
  }

/*---------------- Create default Graphics Context for drawing --------------*/

  drawgc = XCreateGC(display, win, valuemask, &values);

/*----------------------------- specify font ------------------------------- */

  XSetFont(display, drawgc, font_info->fid);

/* -------------------specify foreground and background ---------------------*/

  XSetForeground(display, drawgc, fg_pixel);
  XSetBackground(display,drawgc,bg_pixel);
  c_bgcol=bgcolor;
  c_fgcol=fgcolor;

/*-------------------------- set line attributes ----------------------------*/

  XSetLineAttributes(display, drawgc,line_width,line_style,
                     cap_style,join_style);

/*-------------- set dashes to be line_width in length ----------------------*/

  XSetDashes(display, drawgc, dash_offset, dash_list,2);

/*----------------------------- define stipples -----------------------------*/

  for (i=0;i<17;i++) stipple[i]=
     XCreateBitmapFromData(display,RootWindow(display,screen),patt_pntr[i],8,8);
  XSetFillStyle(display,drawgc,FillOpaqueStippled);

  XSetFunction(display,drawgc,GXcopy);

/*------------------------------- Display window ----------------------------*/

  XMapWindow(display, win);

/*----------------- create region for exposure event processing -------------*/

  region = XCreateRegion();
}

/*____________________________________________________________________________*/

void handleExpose(void (*expose)())

/* this function handles the expose event */

{

  /* set rectangle to be exposed area */
  rectangle.x = (short) report.xexpose.x;
  rectangle.y = (short) report.xexpose.y;
  rectangle.width = (unsigned short) report.xexpose.width;
  rectangle.height = (unsigned short) report.xexpose.height;

  /* union this rect into a region */
  XUnionRectWithRegion(&rectangle, region, region);

  /* if this is the last contiguous expose in a group, set
     the clip region, clear region for next time, and draw.*/
  if (report.xexpose.count == 0)
  {
    XSetRegion(display, drawgc, region);
    XDestroyRegion(region);
    region = XCreateRegion();
    if (expose != NULL) (*expose)();
  }
}

/*____________________________________________________________________________*/

void handleResize(void (*resize)())

/* this function handles the resize event */

{
  /* window has been resized, change width and
   * height to send to place_text and place_graphics
   * in next Expose */

/*   rbiScr = report.xconfigure.width;
     rbjScr = report.xconfigure.height;
*/
   if (resize != NULL) (*resize)();
}

/*____________________________________________________________________________*/

void eventloop(void (*expose)(), void (*resize)(), void (*buttonpress)())

/* This is the main event loop */

{
  for(;;){

    /* get events, use first to display text and graphics */
    XNextEvent(display, &report);

    switch  (report.type)
    {
      case Expose:          handleExpose(expose); break;
      case ConfigureNotify: handleResize(resize);break;
      case ButtonPress:     (*buttonpress)(); break;
      case KeyPress:
           /*****************************
           -- user stuff here for key press in window---
           e.g. exit program (note that, typing q in window exits)
           ******************************/
        XUnloadFont(display, font_info->fid);
        XFreeGC(display, drawgc);
        XCloseDisplay(display);
      default:
        /* all events selected by StructureNotifyMask
         * except ConfigureNotify are thrown away here,
         * since nothing is done with them */
        break;
    }
  }
}

/*____________________________________________________________________________*/

int buttonState=0;
int lastKey=NO_KEY;

void handleEvents(void)

/* This function can be called to handle events instead of entering
   the event loop. The calls must be frequent to ensure proper action.
*/

{
  while (XCheckMaskEvent(display, event_mask, &report))
  switch  (report.type)
  {
    case Expose: handleExpose(NULL);break;
    case ConfigureNotify: handleResize(NULL);break;
    case ButtonPress: buttonState=1;break;
    case ButtonRelease: buttonState=0;break;
    case KeyPress: lastKey=report.xkey.keycode;
    case MotionNotify:
  }
}


/*____________________________________________________________________________*/


static float ratioScr;
static INT myGraphic=0;

void OpenGraphics(INT hres, INT vres, INT bg_col, INT fg_col, INT ltx, INT lty)

/* It opens and displays a graphic window with hres pixels in the horizontal
   direction and vres pixels in the vertical direction with bg_col as the
   background color and fg_col as the foreground color
*/

{
  char nulltxt='\0';
  char *nulltxtPtr=&nulltxt;

  if (isgraphic)
  {

    fontWdth=9;
    fontHght=15;

    opengfxwndw(2,hres,vres,bg_col,fg_col,1,&nulltxtPtr);
    myGraphic=1;

    do{
      XNextEvent(display, &report);
    }while (report.type != Expose);
    handleExpose(NULL);
  }
}

/*____________________________________________________________________________*/

void CloseGraphics(void)
/*it destroys graphic window */
{
  if (myGraphic)
  {
    if (isgraphic)
    {
      XDestroyWindow(display,win);
    }
  }
}

/*____________________________________________________________________________*/

void SetBgCol(INT col)
/* SetBgCol changes the background color to col */
{
  if(isgraphic)
  {
    XSetBackground(display, drawgc,  exact_defs[col].pixel);
    c_bgcol=col;
  }
}

/*____________________________________________________________________________*/

void SetFgCol(INT col)
/* SetFgCol changes the foreground color to col */
{
  if(isgraphic)
  {
    XSetForeground(display, drawgc,  exact_defs[col].pixel);
    c_fgcol=col;
  }
}

/*____________________________________________________________________________*/

void PlotDot(INT i, INT j)
/*The PlotDot function draws a point at i,j */
{
  if (isgraphic)
  {
    XDrawPoint(display,win,drawgc,i,j+top_marg_size);
  }
}

/*____________________________________________________________________________*/

void MoveTo(INT i, INT j)
/* The MoveTo function moves the current drawing position to pixel
   coordinates i,j */
{
  if (isgraphic)
  {
    c_ipstn=i;
    c_jpstn=j+top_marg_size;
  }
}

/*____________________________________________________________________________*/

void LineTo(INT i, INT j)
/* The LineTo function draws a line from the current drawing position to pixel
   coordinates i,j and changes the current drawing coordinates to i,j */
{
  if (isgraphic)
  {
    XDrawLine(display,win,drawgc,c_ipstn,c_jpstn,i,j+top_marg_size);
    c_ipstn=i;
    c_jpstn=j+top_marg_size;
  }
}

/*____________________________________________________________________________*/

void Crcl(INT i, INT j, INT r)
/* The function crcl draws a circle centered at i,j of radius r */
{
  if (isgraphic)
  {
    XDrawArc(display,win,drawgc,i,j+top_marg_size,2*r,2*r,0,2304);
  }
}

/*____________________________________________________________________________*/

void FillRct(RCT *r, INT pattern, INT color)
/* Function FillRct fills the rectangle r with the given pattern in the given
   color. It does not change the current foreground color */
{
if (isgraphic)
{
   XSetStipple(display,drawgc,stipple[pattern]);
   XSetForeground(display,drawgc,exact_defs[color].pixel);
     XFillRectangle(display,win,drawgc,r->lti,r->ltj+top_marg_size,r->rbi-r->lti+2,r->rbj-r->ltj+2+top_marg_size);
   XSetForeground(display,drawgc,exact_defs[c_fgcol].pixel);
   XSetStipple(display,drawgc,stipple[SOLID_P]);
}
}

/*____________________________________________________________________________*/

void DrawStrng(const char *txt)
/* DrawStrng draws the string txt starting from the current drawing position */
{
  if (isgraphic)
  {
    XDrawImageString(display,win,drawgc,c_ipstn,c_jpstn+fontHght,txt,strlen(txt));
  }
}

/*____________________________________________________________________________*/

static Window win_root,win_child;
static int root_x,root_y,win_x,win_y,bttn_mask;

int Button(void)
/* Function Button returns:
   1 if any mouse button is pressed,
   0 if no button is pressed */
{
if (isgraphic)
{
  handleEvents();
//  if(XQueryPointer(display,win,
//                 &win_root,&win_child,&root_x,&root_y,&win_x,&win_y,&bttn_mask))
//  return (bttn_mask);
  return buttonState;
}
}

/*____________________________________________________________________________*/

void GetMouse(PXL *pt)
/* Function GetMouse returns the current position of the pointer or (-1,-1)
   when the pointer is not in the graphic window */
{
  if (isgraphic)
  {
    pt->j=-1;pt->i=-1;
    if(XQueryPointer(display,win,
                     &win_root,&win_child,&root_x,&root_y,&win_x,&win_y,&bttn_mask))
    {
      pt->j=win_y-top_marg_size;
      pt->i=win_x;
    }
  }
}

/*____________________________________________________________________________*/

static struct tms buffer;

DREAL Clock(void)
/* Function Clock returns process time in seconds as a double */
{
  times(&buffer);
  return ((DREAL)(buffer.tms_utime+buffer.tms_stime) /60.0);
}

/*____________________________________________________________________________*/

struct timeval tp;

DREAL RClock(void)
{
  gettimeofday(&tp,NULL);
  return ((DREAL)tp.tv_sec);
}

/*____________________________________________________________________________*/

void Beep(INT freq, INT t)
/* Function Beep rings the bell; freq and time are ignored */
{
  XBell(display,0);
}

/*____________________________________________________________________________*/

struct timeval tp;

char *datetime(void)
{
  gettimeofday(&tp,NULL);
  return (ctime(&tp.tv_sec));
}

/*____________________________________________________________________________*/

int GetKey(void)
{
  long keysym;

  lastKey=NO_KEY;
  handleEvents();
  if (lastKey!=NO_KEY)
  {
    keysym=(long)XKeycodeToKeysym(display,lastKey,0);
    return (int)(keysym & 0x0000FFFF);
  } else {
    return NO_KEY;
  }
}

/*____________________________________________________________________________*/

/// @}
