/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file primitiv.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/frame.h"
#include "capd/capd/minmax.h"
typedef short int SINT;
typedef int INT;
typedef long DINT;
typedef unsigned char BYTE;
typedef unsigned short WORD;
typedef unsigned long DWORD;
typedef float REAL;
typedef double DREAL;

namespace capd{
namespace krak{

   capd::krak::Frame *statFrm=NULL,*goFrm=NULL,*stopFrm=NULL,*exitFrm=NULL,*ctrlFrm=NULL;
   capd::krak::Frame *cFrm=NULL,*rootFrm=NULL;
   int isgraphic=1,graphics_selected;
   int fontHght=F_HGHT,fontWdth=F_WDTH;
   int Hrs,Vrs;
   double scr_ratio;
   void (*restore_window)(void)=default_restore_window;
}}

#if defined(KRAK_ERRORS)
  #include "capd/krak/job.h"
namespace capd{
namespace krak{
   view_job *view_cerr;
   list view;
 }}
#endif

using namespace std;
/*___________________________________________________________________________*/

DWORD capd::krak::EstimFreeMem(void)
{
   DWORD rm0=0,rm1=100000000,rm;
   char HG *ptr;

   do{
      rm=(rm0+rm1)/2;
      if (NULL==(ptr=(char HG *)mlalloc(rm)))
      {
         rm1=rm;
      } else {
         rm0=rm;
         lfree(ptr);
      }
   }while (rm1-rm0>100000);
   return rm0;
}

/*___________________________________________________________________________*/

void capd::krak::closeGraphics(void)

/* It closes the graphics window */

{
   if (capd::krak::isgraphic)
   {
      capd::krak::CloseGraphics();
      capd::krak::graphics_selected=0;
   }
}

/*___________________________________________________________________________*/

/* #################### printf facilities in graphic mode ################## */

/*___________________________________________________________________________*/

void capd::krak::DrawTxtg(capd::krak::Frame *frm, char *buf)

/*DrawTxtg draws the text pointed to by buf
  in the frame frm at the current position
  The '\n' character causes change of line'
*/

{
   char *s=buf;
   char c[256];
   int i,n;
   char ch;

   for(;;){
      i=0;
      while( *s!='\n' && *s!='\0') if ((ch=*s++)!='\r') c[i++]= ch;
      if (frm->cRow <= frm->lRow)
      {
         n=frm->lCol - frm->cCol+1;n=(n>0 ? n : 0);n=(i<n ? i : n);
         c[n]='\0';
         capd::krak::MoveTo( frm->lti + capd::krak::fontWdth * frm->cCol + frm->imarg,
            frm->ltj + capd::krak::fontHght * frm->cRow + frm->jmarg);
         capd::krak::DrawStrng(c);
         frm->cCol+=n;
      }
      if (*s=='\n')
      {
         frm->cRow++;
         frm->cCol=0;
         s++;
      } else {
         break;
      }
   }
}
/*___________________________________________________________________________*/

void capd::krak::DrawTxtc(capd::krak::Frame *frm, char *buf)
{
   capd::krak::SetFgCol(frm->fgColor);
   capd::krak::SetBgCol(frm->bgColor);
   capd::krak::DrawTxtg(frm,buf);
}
/*___________________________________________________________________________*/

void capd::krak::Rctngl_at(capd::krak::Frame *frm, INT lti, INT ltj, INT rbi, INT rbj)
{
   capd::krak::Rctngl(frm->lti + capd::krak::fontWdth*lti,
      frm->ltj + capd::krak::fontHght*ltj,
      frm->lti + capd::krak::fontWdth*rbi,
      frm->ltj + capd::krak::fontHght*rbj);
}

/*___________________________________________________________________________*/
namespace capd{
namespace krak{
void outchar(capd::krak::Frame *frm, INT row, INT col, char ch)

/* It prints a single character ch at the given row and column in the given
   frame
*/

{
   char c[]=" ";

   c[0]=ch;
   capd::krak::MoveTo( frm->lti + capd::krak::fontWdth * col + capd::krak::fontWdth/2,
      frm->ltj + capd::krak::fontHght * (row + 1) );
   capd::krak::DrawStrng(c);
}
}}

/*___________________________________________________________________________*/

void capd::krak::gprintf(capd::krak::Frame *frm,const char *fmt,...)

/* Acts like printf but in graphic mode
   with text starting from the current position
*/

{
   va_list args;
   char buf[256];

   va_start(args,fmt);
   if (frm == NULL)
   {
      printf("Cannot gprintf on a NULL frame\n");
      exit(0);
   } else {
      (void)vsprintf(buf,fmt,args);
      capd::krak::DrawTxtg(frm,buf);
      va_end(args);
   }
}

/*___________________________________________________________________________*/

void capd::krak::gprintf_at(capd::krak::Frame *frm,int row,int col,const char *fmt,...)

/*
   It acts like gprintf but moves the current position
   to the specified row and column
*/

{
   va_list args;
   char buf[256];

   va_start(args,fmt);
   if (frm == NULL)
   {
      printf("Cannot gprintf on a NULL frame\n");exit(0);
   } else {
      frm->cRow=row;
      frm->cCol=col;
      (void)vsprintf(buf,fmt,args);
      capd::krak::DrawTxtg(frm,buf);
   }
   va_end(args);
}

/*___________________________________________________________________________*/

void capd::krak::vgprintf_at(capd::krak::Frame *frm, int row, int col, const char *fmt, va_list args)
{
   char buf[256];

   if (frm == NULL)
   {
      printf("Cannot gprintf on a NULL frame\n");exit(0);
   } else {
      frm->cRow=row;
      frm->cCol=col;
      (void)vsprintf(buf,fmt,args);
      capd::krak::DrawTxtg(frm,buf);
   }
}

/*___________________________________________________________________________*/

void capd::krak::gcprintf(char *fmt,...)

/*
   Like gprintf but with respect to the current frame
*/

{
   va_list args;
   char buf[256];

   va_start(args,fmt);
   (void)vsprintf(buf,fmt,args);
   capd::krak::DrawTxtg(cFrm,buf);
   va_end(args);
}

/*___________________________________________________________________________*/

void capd::krak::gcprintf_at(int row,int col,char *fmt,...)

/*
   Like gprintf_at but with respect to the current frame
*/

{
   va_list args;
   char buf[256];

   va_start(args,fmt);
   cFrm->cRow=row;
   cFrm->cCol=col;
   (void)vsprintf(buf,fmt,args);
   capd::krak::DrawTxtg(cFrm,buf);
   va_end(args);
}

/*___________________________________________________________________________*/

void capd::krak::waitMouseBt(void)

/* it suspends the execution of the program until the button is pressed */

{
   if (capd::krak::isgraphic)
   {
      while(!capd::krak::Button());
      while(capd::krak::Button());
   }
}

/*___________________________________________________________________________*/

void capd::krak::waitBt(void)

/* it suspends the execution of the program until the button is pressed */

{
   if (capd::krak::isgraphic)
   {
      for(;;){
         if(capd::krak::GetKey()!=NO_KEY) break;
         if(capd::krak::Button()) {
            while(capd::krak::Button());
            break;
         }
      }
   }
}

/*___________________________________________________________________________*/

void capd::krak::errorExit(const char *fmt, ... )

/*
   It prints the specified arguments following the specified format:
   - on standart output in a non-graphic run
   - in the middle of the graphics screen in a graphic run
   and it exits
*/

{
   va_list args;

   va_start(args,fmt);
   if (capd::krak::isgraphic)
   {
      vgprintf_at(capd::krak::rootFrm,10,0,fmt,args);
      waitBt();
   } else {
      printf("\n\n\n\n\n");
      vprintf(fmt,args);
      printf("\n");
   }
      capd::krak::closeGraphics();
      va_end(args);
      exit(0);
}

/*___________________________________________________________________________*/

static int warnNo=0;

void capd::krak::warning(const char *fmt,...)

/*
   Like errorExit but it exits only after 100 calls
   to the function warning
*/

{
   va_list args;

   va_start(args,fmt);
   if (capd::krak::isgraphic)
   {
      vgprintf_at(capd::krak::rootFrm,10,0,fmt,args);
   } else {
      vprintf(fmt,args);
   }
      va_end(args);
      warnNo++;
      if (warnNo>100) {
         capd::krak::closeGraphics();
         exit(0);
      }
}

/*___________________________________________________________________________*/

/* ############## Basic drawing routines ################################### */

/*___________________________________________________________________________*/

void capd::krak::moveTo(DREAL x, DREAL y)

/* It moves the current position to the point (x,y)
   specified in the world coordinates
*/

{
   capd::krak::MoveTo(sc_i(x),sc_j(y));
}

/*___________________________________________________________________________*/

void capd::krak::lineTo(DREAL x,DREAL y)

/* It draws a line from the current position to the point (x,y)
   specified in the world coordinates
*/

{
   capd::krak::LineTo(sc_i(x),sc_j(y));
}

/*___________________________________________________________________________*/

void capd::krak::plotDot(DREAL x, DREAL y)

/* It marks the point with the specified world coordinates */

{
   PlotDot(sc_i(x),sc_j(y));
}

/*___________________________________________________________________________*/

void capd::krak::Segment(INT i0, INT j0, INT i1, INT j1)

/*It draws a segment from pixel (i0,j0) to pixel (i1,j1) */

{
   capd::krak::MoveTo(i0,j0);
   capd::krak::LineTo(i1,j1);
}

/*___________________________________________________________________________*/

void capd::krak::Rctngl(INT lti, INT ltj, INT rbi, INT rbj)

/*It draws a rectangle with the specified pixel coordinates
  of the left top and right bottom corner
*/

{
   capd::krak::MoveTo(lti,ltj);
   capd::krak::LineTo(lti,rbj);
   capd::krak::LineTo(rbi,rbj);
   capd::krak::LineTo(rbi,ltj);
   capd::krak::LineTo(lti,ltj);
}

/*___________________________________________________________________________*/

void capd::krak::DrawRct(capd::krak::Rct *r)

/*It draws the rectangle r
*/

{
   capd::krak::MoveTo(r->lti,r->ltj);
   capd::krak::LineTo(r->lti,r->rbj);
   capd::krak::LineTo(r->rbi,r->rbj);
   capd::krak::LineTo(r->rbi,r->ltj);
   capd::krak::LineTo(r->lti,r->ltj);
}

/*___________________________________________________________________________*/


/* ################# Basic shape drawing routines ########################## */

/*___________________________________________________________________________*/

void capd::krak::Square(INT i,INT j, INT size)

/* It draws a square of a given size centered at i,j (pixel coordinates) */

{
   capd::krak::MoveTo(i-size,j-size);
   capd::krak::LineTo(i-size,j+size);
   capd::krak::LineTo(i+size,j+size);
   capd::krak::LineTo(i+size,j-size);
   capd::krak::LineTo(i-size,j-size);
}

/*___________________________________________________________________________*/

void capd::krak::Cross(INT i,INT j, INT size)

/* It draws a cross of a given size centered at i,j (pixel coordinates) */

{
   capd::krak::MoveTo(i,j+size);
   capd::krak::LineTo(i,j-size);
   capd::krak::MoveTo(i-size,j);
   capd::krak::LineTo(i+size,j);
}

/*___________________________________________________________________________*/

void capd::krak::Diamond(INT i,INT j, INT size)

/* It draws a diamond of a given size centered at i,j (pixel coordinates) */

{
   capd::krak::MoveTo(i,j+size);
   capd::krak::LineTo(i-size,j);
   capd::krak::LineTo(i,j-size);
   capd::krak::LineTo(i+size,j);
   capd::krak::LineTo(i,j+size);
}

/*___________________________________________________________________________*/

void capd::krak::Xcross(INT i,INT j, INT size)

/* It draws an X cross of a given size centered at i,j (pixel coordinates) */

{
   capd::krak::MoveTo(i-size,j-size);
   capd::krak::LineTo(i+size,j+size);
   capd::krak::MoveTo(i-size,j+size);
   capd::krak::LineTo(i+size,j-size);
}

/*___________________________________________________________________________*/

/*___________________________________________________________________________*/

void capd::krak::MarkPt3D(capd::krak::Frame *frm, DREAL u, DREAL v, DREAL rb_col)

/* This marks a point using color for 3rd dimension
*/

{
   INT col,c_col;

   selFrm(frm);
//  col=RAINBOW((w+50)/100);
   col=RAINBOW(rb_col);
   c_col=c_fgcol;
   capd::krak::SetFgCol(col);
   capd::krak::PlotDot(sc_i(u),sc_j(v));
   capd::krak::SetFgCol(c_col);
}

/* ################## Frame related functions ############################## */

/*___________________________________________________________________________*/

INT capd::krak::linear(INT x, INT x0, INT y0, INT x1, INT y1)

/* It rescales x from x0,x1 coordinate system to y0,y1 coordinate system */

{
   double fr;
   fr=((double)(x-x0))/((double)(x1-x0));
   return ((INT)(fr*(y1-y0)+y0));
}

/*___________________________________________________________________________*/

void capd::krak::SetRct(capd::krak::Rct *r, INT lti, INT ltj, INT rbi, INT rbj)

/* It assigns given (pixel coordinates) to the rectangle *r */

{
   r->lti=lti;
   r->ltj=ltj;
   r->rbi=rbi;
   r->rbj=rbj;
}

/*___________________________________________________________________________*/

void capd::krak::drawFrm(capd::krak::Frame *frmPtr)

/* it draws (the boundary of) the specified frame */

{
   if (frmPtr==NULL)
      capd::krak::errorExit("Cannot draw a NULL frame");
   capd::krak::Rctngl(frmPtr->lti,frmPtr->ltj,frmPtr->rbi,frmPtr->rbj);
}

/*___________________________________________________________________________*/

void capd::krak::scaleFrm(capd::krak::Frame *frmPtr)

/* it draws scales of the specified frame */

{
   DREAL x,y,xstep=(frmPtr->nex-frmPtr->swx)/6,ystep=(frmPtr->ney-frmPtr->swy)/6;
   INT i,j;
   char buf[15];

   selFrm(frmPtr);

   if (frmPtr==NULL)
      capd::krak::errorExit("Cannot scale a NULL frame");
   for(x=frmPtr->swx+xstep;x<frmPtr->nex-xstep/2;x+=xstep)
   {
      j=sc_j(frmPtr->swy);
      capd::krak::MoveTo(i=sc_i(x),j);
      capd::krak::LineTo(i,j-5);
      capd::krak::MoveTo(i-2*capd::krak::fontWdth,j-8-capd::krak::fontHght);
      sprintf(buf,"%4.1f",x);
      capd::krak::DrawStrng(buf);
   }

   for(y=frmPtr->swy+ystep;y<frmPtr->ney-ystep/2;y+=ystep)
   {
      i=sc_i(frmPtr->swx);
      capd::krak::MoveTo(i,j=sc_j(y));
      capd::krak::LineTo(i+5,j);
      capd::krak::MoveTo(i+10,j-1-capd::krak::fontHght/2);
      sprintf(buf,"%4.1f",y);
      capd::krak::DrawStrng(buf);
   }
}

/*___________________________________________________________________________*/

void capd::krak::clrFrm(capd::krak::Frame *frmPtr)

/* it draws (the boundary of) the specified frame */

{
   if (frmPtr==NULL)
      capd::krak::errorExit("Cannot draw a NULL frame");
   capd::krak::FillRct((capd::krak::Rct *)frmPtr,EMPTY_P,frmPtr->bgColor);
}

/*___________________________________________________________________________*/

void capd::krak::selFrm(capd::krak::Frame *frmPtr)

/* It makes the specified frame the current frame */

{
   if (frmPtr==NULL)
      capd::krak::errorExit("Cannot select a NULL frame");
   cFrm=frmPtr;
}

/*___________________________________________________________________________*/

void capd::krak::dscrFrm(capd::krak::Frame *frm, DREAL swx, DREAL swy, DREAL nex, DREAL ney)

/* It assigns the specified world coordinates to the specified frame */

{
   frm->swx= swx;
   frm->swy= swy;
   frm->nex= nex;
   frm->ney= ney;
}

/*___________________________________________________________________________*/

void capd::krak::initFrm(capd::krak::Frame *frm, INT arglti,INT argltj,INT argrbi, INT argrbj,
      INT bgc, INT fgc, INT im, INT jm)
{
   frm->ci=frm->lti=arglti;
   frm->cj=frm->ltj=argltj;
   frm->rbi=argrbi;
   frm->rbj=argrbj;
   frm->imarg=im;
   frm->jmarg=jm;
   frm->cRow= frm->cCol=0;
   frm->lRow= (frm->rbj - frm->ltj-jm-jm)/capd::krak::fontHght-1;
   frm->lCol= (frm->rbi - frm->lti-im-im)/capd::krak::fontWdth-1;
   cFrm=frm;
   capd::krak::dscrFrm(frm,0.0,0.0,1.0,1.0);
   frm->bgColor=bgc;
   frm->fgColor=fgc;
   frm->prec=6;
}

/*___________________________________________________________________________*/

capd::krak::Frame *capd::krak::openRelFrm(capd::krak::Frame *prntFrm,INT lti,INT ltj,INT rbi,INT rbj)

/* It generates a new frame as a subframe of prntFrm
   with left top corner (lti,ltj),right bottom corner at (rbi,rbj),
   where the coordinates are given in percentage
   of the horizontal and vertical size of the parent frame
*/

{
   capd::krak::Frame *frmPtr;

   if (prntFrm == NULL)
      capd::krak::errorExit("Parent not defined!");
   if ( NULL == (frmPtr=(capd::krak::Frame *)malloc(sizeof(capd::krak::Frame))) )
      capd::krak::errorExit("No Memory for Frame!\n");
//  (*frmPtr).initFrm(
   capd::krak::initFrm(frmPtr,
      capd::krak::linear(lti,(INT)0,prntFrm->lti,(INT)100,prntFrm->rbi),
      capd::krak::linear(ltj,(INT)0,prntFrm->ltj,(INT)100,prntFrm->rbj),
      capd::krak::linear(rbi,(INT)0,prntFrm->lti,(INT)100,prntFrm->rbi),
      capd::krak::linear(rbj,(INT)0,prntFrm->ltj,(INT)100,prntFrm->rbj),
      prntFrm->bgColor, prntFrm->fgColor
   );

   return (frmPtr);
}

/*___________________________________________________________________________*/

capd::krak::Frame *capd::krak::openTRelFrm(capd::krak::Frame *prntFrm,INT frow,INT fcol,INT lrow,INT lcol)

/* It generates a new frame as a subframe of prntFrm
 with left top corner at (fcol,frow),right bottom corner at (lcol,lrow),
   where the coordinates are given as columns and rows of the parent frame.
   The (lcol,lrow) corner is not included in the frame.
*/

{
   capd::krak::Frame *frmPtr;

   if (prntFrm == NULL)
      capd::krak::errorExit("Parent not defined!");
   if ( NULL == (frmPtr=(capd::krak::Frame *)malloc(sizeof(capd::krak::Frame))) )
      capd::krak::errorExit("No Memory for Frame!\n");
//  (*frmPtr).initFrm(
   initFrm(frmPtr,
      prntFrm->lti + fcol*capd::krak::fontWdth,
      prntFrm->ltj + frow*capd::krak::fontHght,
      prntFrm->lti + lcol*capd::krak::fontWdth,
      prntFrm->ltj + lrow*capd::krak::fontHght,
      prntFrm->bgColor, prntFrm->fgColor
   );

   return frmPtr;
}

/*___________________________________________________________________________*/

capd::krak::Frame *capd::krak::opdsRelFrm(capd::krak::Frame *prntFrm,INT lti,INT ltj,INT rbi,INT rbj,
   DREAL swx,DREAL swy,DREAL nex,DREAL ney)

/* As openRelFrm but additionally it assigns world coordinates to the frame */

{
   capd::krak::Frame *frmPtr;

   frmPtr = capd::krak::openRelFrm(prntFrm,lti,ltj,rbi,rbj);
   capd::krak::dscrFrm(frmPtr,swx,swy,nex,ney);
   return (frmPtr);
}

/*___________________________________________________________________________*/

void capd::krak::clseFrm(capd::krak::Frame *frm)

/* It closes the specified frame */

{
   if (frm==NULL)
      capd::krak::errorExit("Cannot close a NULL frame");
   capd::krak::clrFrm(frm);
   free(frm);
}

/*___________________________________________________________________________*/

void capd::krak::Clear(capd::krak::Frame *frm, int color)
{
   capd::krak::Rct r;

   capd::krak::SetRct(&r,frm->lti,frm->ltj,frm->rbi,frm->rbj);
   capd::krak::FillRct(&r,SOLID_P,color);
   frm->cRow=frm->cCol=0;
 }

/*___________________________________________________________________________*/
void capd::krak::openGraphics(int hrs, int vrs, int bgcol, int fgcol, int ltx, int lty)

/*It opens a graphic window with hrs horizontal and vrs vertical pixels.
  bgcol and fgcol specify the backgrounnd and foreground color
*/

{
   if (capd::krak::isgraphic)
   {
      Hrs=hrs;Vrs=vrs;scr_ratio=Hrs/Vrs;
      capd::krak::OpenGraphics(hrs,vrs,bgcol,fgcol,ltx,lty);
//  rootFrame.initFrm(0,0,hrs,vrs,bgcol,fgcol);
      capd::krak::initFrm(&capd::krak::rootFrame,0,0,hrs,vrs,bgcol,fgcol);
      capd::krak::rootFrm = &capd::krak::rootFrame;
      capd::krak::graphics_selected=1;
    #if defined(KRAK_ERRORS)
      capd::krak::view_cerr = new capd::krak::view_job(
         "Error",view,capd::krak::Frame(capd::krak::rootFrame,65,45,99,75,DARKBLUE,YELLOW),1,1);
      view_cerr->launch();
      view_cerr->makeInvisible();
    #endif
   }
   capd::krak::Clear(&capd::krak::rootFrame,bgcol);
}


/*___________________________________________________________________________*/

void capd::krak::redrawCtrlFrm(void)
{
   capd::krak::drawFrm(statFrm);
   capd::krak::drawFrm(stopFrm);
   capd::krak::drawFrm(goFrm);
   capd::krak::drawFrm(exitFrm);
   capd::krak::gprintf_at(statFrm,0,0,"STATUS:");
   capd::krak::gprintf_at(stopFrm,0,0,"PAUSE");
   capd::krak::gprintf_at(exitFrm,0,0,"EXIT");
}

/*___________________________________________________________________________*/

void capd::krak::openCtrlFrm(INT lti, INT ltj, INT rbi, INT rbj)

/* It opens a control frame at the location relative to the root frame
 (in percentages of the root frame height and width)
*/

{
   if(ctrlFrm!=NULL) capd::krak::clseFrm(ctrlFrm);
   if(statFrm!=NULL) capd::krak::clseFrm(statFrm);
   if(stopFrm!=NULL) capd::krak::clseFrm(stopFrm);
   if(goFrm!=NULL) capd::krak::clseFrm(goFrm);
   if(exitFrm!=NULL) capd::krak::clseFrm(exitFrm);
   ctrlFrm = capd::krak::openFrm(lti,ltj,rbi,rbj);
   statFrm = capd::krak::openRelFrm(ctrlFrm,0,0,100,40);
   stopFrm = capd::krak::openRelFrm(ctrlFrm,0,40,100,60);
   goFrm = capd::krak::openRelFrm(ctrlFrm,0,60,100,80);
   exitFrm = capd::krak::openRelFrm(ctrlFrm,0,80,100,100);
   capd::krak::redrawCtrlFrm();
}

/*___________________________________________________________________________*/

INT capd::krak::sc_i(DREAL x)

/* It converts the x world coordinate of the current frame
   to the pixel i coordinate relative to the root frame
*/

{
   return
      (INT)(((x-cFrm->swx)/(cFrm->nex-cFrm->swx))*(cFrm->rbi-cFrm->lti)+cFrm->lti);
}

/*___________________________________________________________________________*/

INT capd::krak::sc_j(DREAL y)

/* It converts the y world coordinate of the current frame
   to the pixel j coordinate relative to the root frame
*/

{
   return
      (INT)((1-(y-cFrm->swy)/(cFrm->ney-cFrm->swy))*(cFrm->rbj-cFrm->ltj)+cFrm->ltj);
}

/*___________________________________________________________________________*/

DREAL capd::krak::x_sc(INT i)

/* It acts like sc_x but in the reverse order */

{
   return (DREAL)(((DREAL)i-cFrm->lti)/(cFrm->rbi-cFrm->lti))*(cFrm->nex-cFrm->swx)+cFrm->swx;
}

/*___________________________________________________________________________*/

DREAL capd::krak::y_sc(INT j)

/* It acts like sc_y but in the reverse order */

{
   return (DREAL)(1-((DREAL)j-cFrm->ltj)/(cFrm->rbj-cFrm->ltj))*(cFrm->ney-cFrm->swy) +cFrm->swy;
}

/*___________________________________________________________________________*/

/* ################# Location tests ######################################## */
/*___________________________________________________________________________*/

INT capd::krak::MouseInFrm(capd::krak::Frame *f)

/* It returns 1 if the currrent mouse location is in the specified frame
   otherwise it returns 0
*/

{
   capd::krak::Pxl p;
   int ret=0;

   if (capd::krak::isgraphic)
   {
      capd::krak::GetMouse(&p);
      ret = PxlInFrm(f,&p);
   }
   return ret;
}

/*___________________________________________________________________________*/

INT capd::krak::in_cFrm(DREAL x, DREAL y)

/* It returns 1 if the specified point (in world coordinates with respect
   to the current frame) is in the specified frame;
   otherwise it returns 0
*/

{
   return (x>=cFrm->swx && x<cFrm->nex && y>=cFrm->swy && y< cFrm->ney);
}

/*___________________________________________________________________________*/

INT capd::krak::inscr(INT i, INT j)

/* It returns 1 if the specified pixel is in the specified frame;
   otherwise it returns 0
*/

{
   return (i>=cFrm->lti && i<cFrm->rbi && j>=cFrm->ltj && j< cFrm->rbj);
}

/*___________________________________________________________________________*/
/* ############# KEYBOARD INPUT ############################################ */
/*___________________________________________________________________________*/

int capd::krak::inchar(void)
{
   int ch;

   while((ch=capd::krak::GetKey()) == NO_KEY);
   return ch;
}

/*___________________________________________________________________________*/

void capd::krak::getline(capd::krak::Frame *frm, INT row, INT col, char *txt)

{
   INT i,txtpos=0;
   char ch;

   capd::krak::gprintf_at(frm,row,col,"%c",'_');
   do{
      ch=inchar();
      for (i=0;i<=txtpos;i++)
         capd::krak::gprintf_at(frm,row,col+i,"%c",' ');
      if (ch == '\b' )
      {
         if (txtpos>0) --txtpos;
      } else {
         *(txt + txtpos++)=ch;
      }
      for (i=0;i<txtpos;i++)
         capd::krak::gprintf_at(frm,row,col+i,"%c",*(txt+i));
      capd::krak::gprintf_at(frm,row,col+txtpos,"%c",'_');
   }while (ch !='\n' && ch !='\r');
   capd::krak::gprintf_at(frm,row,col+txtpos,"%c",' ');
   *(txt+txtpos)='\0';
}

/*___________________________________________________________________________*/
/* ############# PAUSE & EXIT TESTS ######################################## */
/*___________________________________________________________________________*/

static char slash[2]="\\";
static int islash=0;

void capd::krak::testExit(void)

/* Whenever mouse is in the exit frame (defined by openCntrlFrm) it suspends the
   execution and asks if the user wants to exit
*/

{
   if (capd::krak::isgraphic)
   {
      islash=1-islash;
      capd::krak::gprintf_at(exitFrm,0,4,"%c",slash[islash]);
      capd::krak::testPause();
      if (capd::krak::MouseInFrm(exitFrm) || (capd::krak::GetKey()=='E'))
      {
         int lastkey;
         capd::krak::gprintf_at(exitFrm,0,0,"Exit?");
         while(capd::krak::MouseInFrm(exitFrm) && (lastkey=capd::krak::GetKey())==NO_KEY)
            if (capd::krak::Button() || lastkey=='Y')
            {
               capd::krak::closeGraphics();
               exit(0);
            }
            capd::krak::gprintf_at(exitFrm,0,0,"EXIT ");
      }
#   ifdef VIRT_MON
      if(mon_getin_putout(0) == 0)
      {
         capd::krak::closeGraphics();
         capd::krak::gprintf_at(rootFrm,23,0,"Forced to break");
         printf("Forced to break\n");
         exit(0);
      }
#   endif
   }
}

/*___________________________________________________________________________*/

void capd::krak::testPause(void)

/* Whenever mouse is in the stop frame (defined by openCntrlFrm) it suspends the
   execution and asks if the user wants to proceed
*/

{
   if (capd::krak::isgraphic)
   {
   if (capd::krak::MouseInFrm(stopFrm))
   {
      capd::krak::gprintf_at(stopFrm,0,0,"Go&St");
      capd::krak::gprintf_at(goFrm,0,0,"Go?    ");
      while(!(capd::krak::MouseInFrm(stopFrm)||capd::krak::MouseInFrm(goFrm))||!capd::krak::Button() );
      capd::krak::gprintf_at(stopFrm,0,0,"PAUSE");
      capd::krak::gprintf_at(goFrm,0,0,"       ");
   }
   }
}

/*___________________________________________________________________________*/

/* ################### PATTERN DEFINITIONS ################################# */

/*___________________________________________________________________________*/

namespace capd{
namespace krak{
PATTWORD empty_p[]={0,0,0,0, 0,0,0,0},
     solid_p[]={0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF,0xFF},
     hline_p[]={0,0xFF,0,0xFF,0,0xFF,0,0xFF},
     vline_p[]={0x55,0x55,0x55,0x55, 0x55,0x55,0x55,0x55},
     dhline_p[]={0,0,0xFF,0xFF,0,0,0xFF,0xFF},
     dvline_p[]={0x33,0x33,0x33,0x33,0x33,0x33,0x33,0x33},
     dot_p[]={0xAA,0x55,0xAA,0x55,0xAA,0x55,0xAA,0x55},
     ddot_p[]={0xCC,0xCC,0x33,0x33,0xCC,0xCC,0x33,0x33},
     dust_p[]={0x88,0,0,0,0x88,0,0,0},
     ddust_p[]={0,0,0x0C,0x0C,0,0,0,0},
     slash_p[]={0x88,0x11,0x22,0x44,0x88,0x11,0x22,0x44},
     islash_p[]={0x11,0x88,0x44,0x22,0x11,0x88,0x44,0x22},
     whdline_p[]={0xEE,0,0,0,0x77,0,0,0},
     dwhdline_p[]={0xF0,0xF0,0,0,0,0,0,0},
     hash_p[]={0xFF,0x55,0xFF,0x55,0xFF,0x55,0xFF,0x55},
     dhash_p[]={0xFF,0xFF,0x33,0x33,0xFF,0xFF,0x33,0x33},
     whash_p[]={0xEE,0x11,0x11,0x11,0xEE,0x11,0x11,0x11},
     dwhash_p[]={0xF3,0xF3,0x33,0x33,0x33,0x33,0x33,0x33},
     wvline_p[]={0x11,0x11,0x11,0x11,0x11,0x11,0x11,0x11},
     vdot_p[]={0xAA,0xAA,0x55,0x55,0xAA,0xAA,0x55,0x55};

PATTWORD *patt_pntr[]={empty_p,solid_p,hline_p,vline_p,dhline_p,dvline_p,dot_p,ddot_p,
    dust_p,ddust_p,slash_p,islash_p,whdline_p,dwhdline_p,hash_p,dhash_p,
    whash_p,dwhash_p,wvline_p,vdot_p};
}}

/*___________________________________________________________________________*/

/* ################# SOME AUXILIARY FUNCTIONS ############################## */
/*___________________________________________________________________________*/


static DREAL clock_marker;

DREAL capd::krak::time_meter(void)
/*It returns the time passsed from the last call to time_meter */
{
   DREAL c,d;

   c = capd::krak::Clock();
   d = c-clock_marker;
   clock_marker = c;
   return d;
}


static long tick_marker=0;

long capd::krak::tick_meter(void)
/*It returns the time passsed from the last call to clock_marker */
{
   long c,d;
   c = capd::krak::tickClock();
   d = c-tick_marker;
   tick_marker = c;
   return d;
}


/*___________________________________________________________________________*/

/* Macros: setStat("stat"); noStat(); */

/*___________________________________________________________________________*/

void capd::krak::bp(void)

/* It makes a short beep */
{
   capd::krak::Beep(400,100);
}

/*___________________________________________________________________________*/

void capd::krak::stop(void)
/* It terminates the execution of the program but first closes
   the graphics package
*/
{
   capd::krak::bp();
   capd::krak::closeGraphics();
   exit(0);
}

/*___________________________________________________________________________*/

void capd::krak::delay(double sleepTime)
/* It delays the execution by sleepTime in seconds
*/
{
   double time = capd::krak::Clock();
   volatile int i;
   while (capd::krak::Clock()-time<sleepTime) i++;
}

/*___________________________________________________________________________*/

void capd::krak::struct_copy(void *from, void *to, INT size)

/* It moves a structure of a given size between the specified
   locations in memory
*/

{
   while(--size >= 0) *((BYTE *)to + size)=*((BYTE *)from + size);
}

/*___________________________________________________________________________*/

/* ################# SIMPLE DEBUGGING FACILITIES ########################### */

/*___________________________________________________________________________*/

capd::krak::Frame *dbgFrm,*brkFrm,*valFrm;

void capd::krak::openDbgFrm(INT lti, INT ltj, INT rbi, INT rbj)

/* It opens windows for debugging in the specified region
   of the screen ( in percentage of the screen sizes)
*/

{
   dbgFrm = capd::krak::openFrm(lti,ltj,rbi,rbj);
   brkFrm = capd::krak::openRelFrm(dbgFrm,0,0,100,20);
   valFrm = capd::krak::openRelFrm(dbgFrm,0,20,100,100);
}

/*___________________________________________________________________________*/

extern capd::krak::Frame *stopFrm;

void capd::krak::vv(INT i, DREAL r)
/* It prints the double r in the line i of the debug window */
{
   capd::krak::drawFrm(valFrm);
   capd::krak::gprintf_at(valFrm,0,0,"VALUES");
   capd::krak::gprintf_at(valFrm,i+1,0,"V%2d=%11.5lf",i,r);
}

/*___________________________________________________________________________*/

void capd::krak::ww(INT i, DREAL r)
/* It acts as the above function but only when the mouse is in the stop
   window
*/
{
   if(capd::krak::MouseInFrm(stopFrm))
   {
      capd::krak::drawFrm(valFrm);
      capd::krak::gprintf_at(valFrm,0,0,"VALUES");
      capd::krak::gprintf_at(valFrm,i+1,0,"V%2d=%11.5lf",i,r);
   }
}

/*___________________________________________________________________________*/

void capd::krak::qq(INT b)
/* It halts the execution reporting Break b
   and waits for Button being pressed.
   If the mouse is in the stop frame when the
   button is pressed, the program is terminated
*/
{
   capd::krak::drawFrm(brkFrm);
   capd::krak::gprintf_at(brkFrm,0,0,"Break %d",b);
   capd::krak::waitBt();
   if (capd::krak::MouseInFrm(stopFrm)) exit(0);
}

/*___________________________________________________________________________*/

void capd::krak::pp(void)
/* It halts the execution if mouse is in the stop frame */
{
   if(capd::krak::MouseInFrm(stopFrm)) capd::krak::waitBt();
}

/*___________________________________________________________________________*/

void capd::krak::default_restore_window(void)
{
   if(capd::krak::rootFrm!=NULL)
   {
      long n=10000000;
      capd::krak::gprintf_at(capd::krak::rootFrm,20,30,"WINDOW CONTENTS LOST");
      while(n-- > 0);
         capd::krak::gprintf_at(capd::krak::rootFrm,20,30,"                    ");
   }
}

/*___________________________________________________________________________*/

/// @}
