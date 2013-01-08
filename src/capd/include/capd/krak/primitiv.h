/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file primitiv.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_PRIMITIV_H_ 
#define _CAPD_KRAK_PRIMITIV_H_ 

#include <cstdarg>
#include "capd/krak/hardware.h"
#include "capd/krak/kernel.h"

#include "capd/krak/frstring.h"

/* Basic drawing routines */
namespace capd{
namespace krak{
   void waitBt(void);
   void waitMouseBt(void);
   void errorExit(const char *fmt,...);
   void warning(const char *fmt,...);
   void moveTo(double x,double y);
   void lineTo(double x,double y);
   void plotDot(double x,double y);
   void Segment(int i0,int j0,int i1,int j1);
   void Rctngl(int lti,int ltj,int rbi,int rbj);
   void DrawRct(capd::krak::Rct *r);
   void Square(int i,int j,int size);
   void Cross(int i,int j,int size);
   void Diamond(int i,int j,int size);
   void Xcross(int i,int j,int size);
   int linear(int x,int x0,int y0,int x1,int y1);
   void SetRct(capd::krak::Rct *r,int lti,int ltj,int rbi,int rbj);

/* constants definitions */

//#define NO_KEY 0xff


//#include "krak/pattern.h"
//   typedef short int SINT;
//   typedef int INT;
   typedef long DINT;
//   typedef unsigned char BYTE;
//   typedef unsigned short WORD;
//   typedef unsigned long DWORD;
//   typedef float REAL;
//   typedef double DREAL;
//   typedef DREAL VECTOR[VDIM];

typedef DINT HG * DINT_P;
typedef char HG * CHAR_P;
typedef unsigned char HG * BYTE_P;

class Frame;

extern int fontHght,fontWdth;
extern capd::krak::Frame *cFrm;
extern capd::krak::Frame rootFrame;

extern capd::krak::Frame *rootFrm;
extern char colorname[24][24];
extern int gray[];
extern int c_bgcol,c_fgcol;
}}

/* macro definitions */

#define openGW openGraphics
#define closeGW closeGraphics
#define dscrGW(a,b,c,d) dscrFrm(rootFrm,a,b,c,d)
#define setRct(r,a,b,c,d) SetRct(r,sc_i(a),sc_j(d),sc_i(c),sc_j(b))
#define drawRct(r) DrawRct(r)
#define rctngl(a,b,c,d) Rctngl(sc_i(a),sc_j(d),sc_i(c),sc_j(b))
#define segment(a,b,c,d) Segment(sc_i(a),sc_j(b),sc_i(c),sc_j(d))
#define cross(x,y,s) Cross(sc_i(x),sc_j(y),s)
#define crcl(x,y,s) Crcl(sc_i(x),sc_j(y),s)
#define square(x,y,s) Square(sc_i(x),sc_j(y),s)
#define diamond(x,y,s) Diamond(sc_i(x),sc_j(y),s)
#define xcross(x,y,s) Xcross(sc_i(x),sc_j(y),s)
#define PxlInFrm(f,p) ((p)->i>=(f)->lti && (p)->i<(f)->rbi && (p)->j>=(f)->ltj && (p)->j< (f)->rbj)
#define openFrm(a,b,c,d) openRelFrm(rootFrm,a,b,c,d)
#define opdsFrm(a,b,c,d,e,f,g,h) opdsRelFrm(rootFrm,a,b,c,d,e,f,g,h)

/* functions declarations */
namespace capd{
namespace krak{
   unsigned long EstimFreeMem(void);
}}
#ifndef MAC
namespace capd{
namespace krak{
   double Clock();
}}
#endif

namespace capd{
namespace krak{
   extern void (*restore_window)(void);

   double tr_cubic(double t);
   void set_col(void);
   void set_pat(void);
   void free_pat(void);

   void MarkPt3D(capd::krak::Frame *frm, double u, double v, double rb_col);

   void closeGraphics(void);
   void DrawTxtg(capd::krak::Frame *frm,char *buf);
   void DrawTxtc(capd::krak::Frame *frm,char *buf);
   void Rctngl_at(capd::krak::Frame *frm,int lti,int ltj,int rbi,int rbj);
   void outchar(capd::krak::Frame *frm,int row,int col,char * ch);
   void gprintf(capd::krak::Frame *frm,const char *fmt,...);
   void gprintf_at(capd::krak::Frame *frm,int row,int col,const char *fmt,...);
   void gcprintf(char *fmt,...);
   void gcprintf_at(int row,int col,char *fmt,...);
   void vgprintf_at(capd::krak::Frame *frm,int row,int col,const char *fmt,std::va_list args);
   void drawFrm(capd::krak::Frame *frmPtr);
   void scaleFrm(capd::krak::Frame *frmPtr);
   void clrFrm(capd::krak::Frame *frmPtr);
   void selFrm(capd::krak::Frame *frmPtr);
   void initFrm(capd::krak::Frame *frmPtr, int arglti,int argltj,int argrbi, int argrbj,
      int bgc=WHITE, int fgc=BLACK,
      int im = capd::krak::fontHght/2, int jm = capd::krak::fontWdth/2
   );
   void dscrFrm(capd::krak::Frame *frm,double swx,double swy,double nex,double ney);
   capd::krak::Frame *openRelFrm(capd::krak::Frame *prntFrm,int lti,int ltj,int rbi,int rbj);
   capd::krak::Frame *openTRelFrm(capd::krak::Frame *prntFrm,int ,int ,int ,int );
   capd::krak::Frame *opdsRelFrm(capd::krak::Frame *prntFrm,int lti,int ltj,int rbi,int rbj,
      double swx,double swy,double nex,double ney);
   void clseFrm(capd::krak::Frame *frm);
   void Clear(capd::krak::Frame *frm, int color);
   void openGraphics(int hrs,int vrs,int bgcol,int fgcol,int ltx=0,int lty=0);
   void redrawCtrlFrm(void);
   void openCtrlFrm(int lti,int ltj,int rbi,int rbj);
   int sc_i(double x);
   int sc_j(double y);
   double x_sc(int i);
   double y_sc(int j);
   int MouseInFrm(capd::krak::Frame *f);
   int in_cFrm(double x,double y);
   int inscr(int i,int j);
   int inchar(void);
   void getline(capd::krak::Frame *frm,int row,int col,char *txt);
   void testExit(void);
   void testPause(void);
   double time_meter(void);
   long tick_meter(void);
   void bp(void);
   void stop(void);
   void delay(double sleepTime);
   void struct_copy(void *from,void *to,int size);
   double DREALmin(int count,double x);
   void openDbgFrm(int lti,int ltj,int rbi,int rbj);
   void vv(int i,double r);
   void ww(int i,double r);
   void qq(int b);
   void pp(void);
   void default_restore_window(void);

#ifdef DOS16
   void myfread(CHAR_P ptr,int size,int n,FILE *f);
   void myfwrite(CHAR_P ptr,int size,int n,FILE *f);
#endif

   void pause(int i,int j, capd::krak::frstring s);
}} // the end of the namespace capd::krak

#endif // _CAPD_KRAK_PRIMITIV_H_ 

/// @}
