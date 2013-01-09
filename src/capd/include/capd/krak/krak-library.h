/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file krak-library.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

/*
   This is the include file for the compiled krak library
   Author: Marian Mrozek
*/

#include <strstream>
namespace capd{
namespace krak{


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

/* Basic color definitions */

#define WHITE       0
#define BLACK       1
#define RED         2
#define GREEN       3
#define BLUE        4
#define YELLOW      5
#define MAGENTA     6
#define CYAN        7
#define ORANGE      8
#define VIOLET      9
#define PINE       10
#define BROWN      11
#define OLIVE      12
#define DARKBLUE   13
#define ORANGERED  14
#define BLUEGREEN  15

#define FRAME_FG   -1
#define FRAME_BG   -2

/* Pattern definitions */

#define MAX_PATTERN_NO 17

#define EMPTY_P     0
#define SOLID_P     1
#define HLINE_P     2
#define VLINE_P     3
#define DHLINE_P    4
#define DVLINE_P    5
#define DOT_P       6
#define DDOT_P      7
#define DUST_P      8
#define DDUST_P     9
#define SLASH_P    10
#define ISLASH_P   11
#define WHDLINE_P  12
#define DWHDLINE_P 13
#define HASH_P     14
#define DHASH_P    15
#define WHASH_P    16
#define DWHASH_P   17
#define WVLINE_P   18
#define VDOT_P     19


#define gout rootFrame
#define main mainEntry

#define NO_KEY 0x1ff
#define DRAG_KEY 0x1fd
#define BUTTON_KEY 0x1fe

enum FunctKeys{BSKey=8,TabKey,CRKey=13,PgUpKey,PgDnKey,EndKey,HomeKey,
    LeftKey,UpKey,RightKey,DownKey,
    InsKey,DelKey,EscKey=27,
          F1Key=89,F2Key,F3Key,F4Key,F5Key,F6Key,F7Key,F8Key,F9Key,
    DragKey=DRAG_KEY,ButtonKey=BUTTON_KEY,NoKey=NO_KEY};

/* structure definitions */

class Frame;
class frstring;
class colstring;

struct Pxl{
  int j,i;
};
typedef struct Pxl PXL;

struct Rct{
  int ltj,lti,rbj,rbi;
};
typedef struct Rct RCT;

/* Externals */

extern int fontHght,fontWdth;
extern Frame rootFrame;
extern Frame *rootFrm;
extern void (*restore_window)(void);


// ###############################  Manipulators ########################

class At{
  public:
  int row,col;
  At(int r,int c);
};

class Tab{
  public:
  int col;
  Tab(int c);
};

class FgColor{
  public:
  int color;
  FgColor(int c);
};

class BgColor{
  public:
  int color;
  BgColor(int c);
};


void SetBgCol(int col);
void SetFgCol(int col);



/* hardware dependant primitives */

void OpenGraphics(int hrs,int vrs,int bgcol,int fgcol,int ltx, int lty);
void CloseGraphics(void);
void MWLineTo(int i,int j);
void MoveTo(int i,int j);
void PlotDot(int i,int j);
void Crcl(int i,int j,int r);
void DrawStrng(char *txt);
void FillRct(RCT *r,int pattNr,int colNr);
void FillChord(int ltj, int lti, int rbj, int rbi, int bj, int bi, int ej, int ei, int pattNr, int colNr);
void Arc(int ltj, int lti, int rbj, int rbi, int bj, int bi, int ej, int ei, int colNr);
void FillRgn(int *r, int lPoints, int pattNr, int colNr);
void GetMouse(PXL *pxl);
int Button(void);
double Clock(void);
long tickClock(void);
double RClock(void);
double tck2sec(long);
void Beep(int freq,int time);
char *datetime(void);
int GetKey(void);

void SetTextSize(int);
int GetTextSize(void);

/* Basic drawing routines */

void waitBt(void);
void waitMouseBt(void);
void errorExit(const char *fmt,...);
void warning(const char *fmt,...);
void moveTo(double x,double y);
void lineTo(double x,double y);
void plotDot(double x,double y);
void Segment(int i0,int j0,int i1,int j1);
void Rctngl(int lti,int ltj,int rbi,int rbj);
void DrawRct(RCT *r);
void Square(int i,int j,int size);
void Cross(int i,int j,int size);
void Diamond(int i,int j,int size);
void Xcross(int i,int j,int size);
int linear(int x,int x0,int y0,int x1,int y1);
void SetRct(RCT *r,int lti,int ltj,int rbi,int rbj);

/* other functions declarations */

double Clock(void);
void delay(double t);
unsigned long EstimFreeMem(void);



double tr_cubic(double t);
void set_col(void);
void set_pat(void);
void free_pat(void);

void MarkPt3D(Frame *frm, double u, double v, double rb_col);

void closeGraphics(void);
void DrawTxtg(Frame *frm,char *buf);
void DrawTxtc(Frame *frm,char *buf);
void Rctngl_at(Frame *frm,int lti,int ltj,int rbi,int rbj);
void outchar(Frame *frm,int row,int col,char * ch);
void gprintf(Frame *frm,char *fmt,...);
void gprintf_at(Frame *frm,int row,int col,char *fmt,...);
void gcprintf(char *fmt,...);
void gcprintf_at(int row,int col,char *fmt,...);
//void vgprintf_at(Frame *frm,int row,int col,char *fmt,va_list args);
void drawFrm(Frame *frmPtr);
void scaleFrm(Frame *frmPtr);
void clrFrm(Frame *frmPtr);
void selFrm(Frame *frmPtr);
void initFrm(Frame *frmPtr, int arglti,int argltj,int argrbi, int argrbj,
               int bgc=WHITE, int fgc=BLACK,
               int im=fontHght/2, int jm=fontWdth/2);
void dscrFrm(Frame *frm,double swx,double swy,double nex,double ney);
Frame *openRelFrm(Frame *prntFrm,int lti,int ltj,int rbi,int rbj);
Frame *openTRelFrm(Frame *prntFrm,int ,int ,int ,int );
Frame *opdsRelFrm(Frame *prntFrm,int lti,int ltj,int rbi,int rbj,double swx,double swy,double nex,double ney);
void clseFrm(Frame *frm);
void Clear(Frame *frm, int color);
void openGraphics(int hrs,int vrs,int bgcol,int fgcol,int ltx=0,int lty=0);
void redrawCtrlFrm(void);
void openCtrlFrm(int lti,int ltj,int rbi,int rbj);
int sc_i(double x);
int sc_j(double y);
double x_sc(int i);
double y_sc(int j);
int MouseInFrm(Frame *f);
int in_cFrm(double x,double y);
int inscr(int i,int j);
int inchar(void);
void getline(Frame *frm,int row,int col,char *txt);
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

void pause(int i,int j, frstring s);




// ###############################  inline definitions ########################

inline At::At(int r,int c){
  row=r;col=c;
}

inline Tab::Tab(int c){
   col=c;
}

inline FgColor::FgColor(int c){
  color=c;
}

inline BgColor::BgColor(int c){
  color=c;
}


// ###############################  class Frame ########################

class Frame{
  public:
  int ltj,lti,rbj,rbi,cj,ci;
  int imarg,jmarg;
  double swx,swy,nex,ney;
  int cRow,cCol,lRow,lCol;
  int bgColor,fgColor;
  int prec;

  void initFrm(int arglti,int argltj,int argrbi, int argrbj,
               int bgc=WHITE, int fgc=BLACK,
               int im=fontHght/2, int jm=fontWdth/2);
  Frame(void);
  Frame(int lti,int ltj,int rbi,int rbj,
        int bgc=WHITE,int fgc=BLACK,
        int im=fontWdth/2, int jm=fontHght/2);
  Frame(const Frame &prntFrm,const At &lt,const At &rb,
        int bgc=WHITE,int fgc=BLACK,
        int im=fontWdth/2, int jm=fontHght/2);
  Frame(Frame &prntFrm,int lti,int ltj,int rbi,int rbj,
        int bgc=WHITE,int fgc=BLACK,
        int im=fontHght/2, int jm=fontWdth/2);
  Frame(Frame &prntFrm,int lti,int ltj,int rbi,int rbj,
        double swx,double swy,double nex,double ney,
        int bgc=WHITE,int fgc=BLACK,
        int im=fontHght/2, int jm=fontWdth/2);
  void Locate(Frame &prntFrm, At &lt, At &rb);
  void Locate(Frame &prntFrm,int lti,int ltj,int rbi,int rbj);
  void setWorldCoord(double swx,double swy,double nex,double ney);

  void adjust(void);

  int NoCol(void);
  int NoRow(void);

  void Clear(void);
  void Clear(int color);
  void Bound(int color=BLACK);


  void SetBgColor(int c);
  void SetFgColor(int c);

  int getRow(PXL &pxl);
  int getCol(PXL &pxl);

  int x2i(double x);
  int y2j(double y);

  double x2p(double x);
  double y2q(double y);

  double i2x(int i);
  double j2y(int j);

  void jump(int i,int j);
  void draw(int i,int j,int color=FRAME_FG);
  void drawText(char *c,int i,int j,int color=FRAME_FG);
  void dot(int i,int j,int color=FRAME_FG);
  void circle(int i,int j,int r, int color=FRAME_FG);
  void line(int i1,int j1,int i2,int j2,int color=FRAME_FG);
  void box(int lti,int ltj,int rbi,int rbj,int color=FRAME_FG);
  void boxFill(int lti,int ltj,int rbi,int rbj,int col,int pattern=SOLID_P);

  void polygon(int coords[],int nPoints,int color=FRAME_FG);
  void polygonFill(int coords[],int nPoints,int col,int pattern=SOLID_P);
  void arc(int lti,int ltj,int rbi,int rbj,int bi,int bj,int ei,int ej,int color=FRAME_FG);
  void arcFill(int lti,int ltj,int rbi,int rbj,int bi,int bj,int ei,int ej,int col,int pattern=SOLID_P);
  void ellipse(int lti,int ltj,int rbi,int rbj,int color=FRAME_FG);
  void ellipseFill(int lti,int ltj,int rbi,int rbj,int col,int pattern=SOLID_P);

  void jump(double x,double y);
  void draw(double x,double y,int color=FRAME_FG);
  void dot(double x,double y,int color=FRAME_FG);
  void circle(double x,double y,int r, int color=FRAME_FG);
  void line(double x1,double y1,double x2,double y2, int color=FRAME_FG);
  void box(double swx,double swy, double nex, double ney,int color=FRAME_FG);
  void boxFill(double swx,double swy, double nex, double ney,int col,int pattern=SOLID_P);

  void polygon(double coords[],int nPoints,int color=FRAME_FG);
  void polygonFill(double coords[],int nPoints,int col,int pattern=SOLID_P);
  void arc(double swx,double swy, double nex, double ney,double bx,double by,double ex,double ey,int color=FRAME_FG);
  void arcFill(double swx,double swy, double nex, double ney,double bx,double by,double ex,double ey,int col,int pattern=SOLID_P);
  void ellipse(double swx,double swy, double nex, double ney,int color=FRAME_FG);
  void ellipseFill(double swx,double swy, double nex, double ney,int col,int pattern=SOLID_P);

  void Xcrss(double x,double y,int size=1, int color=FRAME_FG);

  int precision(int p){prec = p; return p;};

  Frame &operator<<(char c);
  Frame &operator<<(int n);
  Frame &operator<<(long n);
  Frame &operator<<(double r);

  Frame &operator<<(const frstring &a_string);
  Frame &operator<<(char *text);
  Frame &operator<<(colstring &a_colstring);

  Frame &operator<<(const FgColor &c);
  Frame &operator<<(const BgColor &c);
  friend Frame &operator<<(Frame &f,const  At &at);
  Frame &operator<<(Tab tab);


  Frame &operator>>(const At &at);
  Frame &operator>>(const FgColor &c);
  Frame &operator>>(const BgColor &c);

  int isInside(PXL &p);

  Frame &operator>>(frstring &a_string);
  Frame &operator>>(int &n);
  Frame &operator>>(long &n);
  Frame &operator>>(double &r);
  int Edit(At at, int no_col, frstring &s);

};

/* class UserMove */

class UserMove{
public:
 int key;
 capd::krak::Pxl pxl;

 UserMove(void);
};

void SetUserMove(UserMove &um);
int GetUserMove(UserMove &um);
void WaitUserMove(UserMove& um, capd::krak::Rct &r, int col1, int col2, double freq);
void WaitUserMove(UserMove& um);

/* Graphic window routines */

void clear(int color=WHITE);

/* Basic drawing routines in device coordinates */

void jump(int i,int j);
void draw(int i,int j,int color=FRAME_FG);
void drawText(char *c,int i, int j, int  color=FRAME_FG);
void dot(int i,int j,int color=FRAME_FG);
void circ(int pixelRow,int pixelColumn,int r, int color=FRAME_FG);
void circFill(int pixelRow,int pixelColumn,int r, int color=FRAME_FG,int pattern=SOLID_P);
void box(int lti,int ltj,int rbi,int rbj,int color=FRAME_FG);
void boxFill(int lti,int ltj,int rbi,int rbj,int color=FRAME_FG,int pattern=SOLID_P);
void polygon(int coords[],int nPoints,int color=FRAME_FG);
void polygonFill(int coords[],int nPoints,int color=FRAME_FG,int pattern=SOLID_P);
void arc(int leftTopPixelRow,int leftTopPixelColumn,
         int rightBottomPixelRow,int rightBottomPixelColumn,
         int begPixelRow,int begPixelColumn,int endPixelRow,int endPixelColumn,
         int color=FRAME_FG);
void arcFill(int leftTopPixelRow,int leftTopPixelColumn,
         int rightBottomPixelRow,int rightBottomPixelColumn,
         int begPixelRow,int begPixelColumn,int endPixelRow,int endPixelColumn,
         int color=FRAME_FG,int pattern=SOLID_P);
void ellipse(int leftTopPixelRow,int leftTopPixelColumn,
         int rightBottomPixelRow,int rightBottomPixelColumn,int color=FRAME_FG);
void ellipseFill(int leftTopPixelRow,int leftTopPixelColumn,
         int rightBottomPixelRow,int rightBottomPixelColumn,int color=FRAME_FG,int pattern=SOLID_P);

void keyAndMouse(int &key, int &row, int &col);
void mouse(int &row, int &col);

/* Basic drawing routines in world coordinates */

void setWorldCoord(double leftBottomX,double leftBottomY,
         double rightTopX,double rightTopY);
void jump(double x,double y);
void draw(double x,double y,int color=FRAME_FG);
void drawText(char *c,double x, double y, int  color=FRAME_FG);
void dot(double x,double y,int color=FRAME_FG);
void circ(double x,double y,double r, int color=FRAME_FG);
void circFill(double x,double y,double r, int color=FRAME_FG,int pattern=SOLID_P);
void box(double leftBottomX,double leftBottomY,
         double rightTopX,double rightTopY,int color=FRAME_FG);
void boxFill(double leftBottomX,double leftBottomY,
             double rightTopX,double rightTopY,int color=FRAME_FG,int pattern=SOLID_P);
void polygon(double coords[],int nPoints,int color=FRAME_FG);
void polygonFill(double coords[],int nPoints,int color=FRAME_FG,int pattern=SOLID_P);
void arc(double leftBottomX,double leftBottomY,
         double rightTopX,double rightTopY,
         double begX,double begY,double endX,double endY,
         int color=FRAME_FG);
void arcFill(double leftBottomX,double leftBottomY,
         double rightTopX,double rightTopY,
         double begX,double begY,double endX,double endY,
         int color=FRAME_FG,int pattern=SOLID_P);
void ellipse(double swx,double swy, double nex, double ney,int color=FRAME_FG);
void ellipseFill(double swx,double swy, double nex, double ney,int color=FRAME_FG,int pattern=SOLID_P);

void keyAndMouse(int &key, double& x,double& y);
void mouse(double x,double y);

/* Basic mouse and keybord routines */

int  button(void);
void waitButton(void);

void setTextSize(int size);
int getTextSize(void);
void setBackgroundColor(int color);
void setForegroundColor(int color);

//###################### TEMPLATES DEFINITIONS ####################################


// A universal template for outputting anything to a frame via a string.
template <class type>
Frame &operator << (Frame &f, const type &x){
 std::ostrstream s;
 s << x << ends;
 char *str = s. str ();
 f << str;
 delete [] str;
 return f;
} /* operator << */


// ###############################  inline definitions ########################

inline void Frame::adjust(void){
  lti=lti/fontWdth*fontWdth;
  ltj=ltj/fontHght*fontHght;
  rbi=rbi/fontWdth*fontWdth;
  rbj=rbj/fontHght*fontHght;
  lRow= (rbj - ltj-jmarg-jmarg)/fontHght-1;
  lCol= (rbi - lti-imarg-imarg)/fontWdth-1;
};

/**
@doc
  Return the number of columns in the frame
*/
inline int Frame::NoCol(void){
  return (rbi - lti - imarg - imarg)/fontWdth;
};

/**
@doc
  Return the number of rows in the frame
*/
inline int Frame::NoRow(void){
  return (rbj - ltj - jmarg - jmarg)/fontHght;
};

/**
@doc
  Sets to world coordinates.
  @param swx,swy the coordinates of the bottom-left (southwest) corner
  @param nex,ney the coordinates of the upper-right (northeast) corner
*/
inline void Frame::setWorldCoord(double the_swx,double the_swy,
                                 double the_nex,double the_ney){
  dscrFrm(this,the_swx,the_swy,the_nex,the_ney);
};

/**
@doc
  Clears the frame with the background color and moves
  the current position to (0,0)
*/
inline void Frame::Clear(void){
  RCT r;

  SetRct(&r,lti,ltj,rbi,rbj);
  FillRct(&r,SOLID_P,bgColor);
  cRow=cCol=0;
};

/**
@doc
  Clears the frame with the color @i(color) and moves
  the current position to (0,0)
*/
inline void Frame::Clear(int color){
  RCT r;

  SetRct(&r,lti,ltj,rbi,rbj);
  FillRct(&r,SOLID_P,color);
  cRow=cCol=0;
};

/**
@doc
  Draw a boundary around the frame in color @i(color)
*/
inline void Frame::Bound(int color){
  SetFgCol(color);
  Rctngl(lti,ltj,rbi,rbj);
};

/**
@doc
  Sets the background color to @i(c).
*/
inline void Frame::SetBgColor(int c){
  bgColor=c;
};

/**
@doc
  Sets the foreground color to @i(c).
*/
inline void Frame::SetFgColor(int c){
  fgColor=c;
};

/**
@doc
  returns the character row that correspond to the pixel @i(pxl)
*/
inline int Frame::getRow(PXL &pxl){
  return (pxl.j-ltj-jmarg)/fontHght;
};

/**
@doc
  returns the character column that correspond to the pixel @i(pxl)
*/
inline int Frame::getCol(PXL &pxl){
  return (pxl.i-lti-imarg)/fontWdth;
};

/**
@doc
Changes the foreground color of the frame, like:
<pre>
frm<< FgColor(RED)<<"red "<< FgColor(BLUE)<<"blue"
</pre>
*/
inline Frame &Frame::operator<<(const FgColor &c){
  SetFgColor(c.color);
  return *this;
};

/**
@doc
Changes the background color of the frame, like:
<pre>
frm<< BgColor(YELLOW)<<"yellow"<< BgColor(GREEN)<<"green"
</pre>
*/
inline Frame &Frame::operator<<(const BgColor &c){
  SetBgColor(c.color);
  return *this;
};

/**
@doc
  Moves the current position to the cell refered by @i(at), like:
<pre>
frm<<At(30,30)<<"AAAAA";
</pre>
*/
inline Frame &operator<<(Frame &f,const  At &at){
  f.cCol=at.col;
  f.cRow=at.row;
  return f;
};

/**
@doc
  Moves the current position to the column refered by @i(tab)
*/
inline Frame &Frame::operator<<(Tab tab){
  cCol=tab.col;
  return *this;
};

/**
@doc
  Translates world coordinate @i(x) to a device coordinate
*/
inline int Frame::x2i(double x){
  return (int)(((x-swx)/(nex-swx))*(rbi-lti)+lti);
};

/**
@doc
  Translates world coordinate @i(y) to a device coordinate
*/
inline int Frame::y2j(double y){
  return (int)((1-(y-swy)/(ney-swy))*(rbj-ltj)+ltj);
};

/**
@doc
  Same as @ref<x2i()> but returns a double
*/
inline double Frame::x2p(double x){
  return (((x-swx)/(nex-swx))*(rbi-lti)+lti);
};

/**
@doc
  Same as @ref<y2j()> but returns a double
*/
inline double Frame::y2q(double y){
  return ((1-(y-swy)/(ney-swy))*(rbj-ltj)+ltj);
};

/**
@doc
  Translates device coordinate @i(i) to a world coordinate
*/
inline double Frame::i2x(int i){
  return (double)(((double)i-lti)/(rbi-lti))*(nex-swx)+swx;
};

/**
@doc
  Translates device coordinate @i(j) to a world coordinate
*/
inline double Frame::j2y(int j){
  return (double)(1-((double)j-ltj)/(rbj-ltj))*(ney-swy)+swy;
};

/**
@doc
  Moves the current position to (@i(i), @i(j)), in device coordinates
*/
inline void Frame::jump(int i,int j){
  ci=i;cj=j;
};

/**
@doc
  Moves the current position to (@i(x), @i(y)), in world coordinates
*/
inline void Frame::jump(double x,double y){
  jump(x2i(x),y2j(y));
};

/**
@doc
  Draws a line from from the current position to (@i(x), @i(y)) (in world
  coordinates) using the color @i(color)
*/
inline void Frame::draw(double x,double y,int color){
  draw(x2i(x),y2j(y),color);
};

/**
@doc
  draws a box (an empty rectangle) with the left top corner in
  (@i(lti), @i(ltj)) and the right botton corner in (@i(rbi), @i(rbj)), in
  device coordinates.
@param color The color of the box. If it is FRAME_FG then the frame
  foreground color is used
*/
inline void Frame::box(int lti,int ltj,int rbi,int rbj,int color){
  jump(lti,ltj);
  draw(lti,rbj,color);
  draw(rbi,rbj,color);
  draw(rbi,ltj,color);
  draw(lti,ltj,color);
};

/**
@doc
  draws a box (an empty rectangle) with the left botton corner in
  (@i(swx), @i(swy)) and the right top corner in (@i(nex), @i(ney)), in
  world coordinates.
@param color The color of the box. If it is FRAME_FG then the frame
  foreground color is used
*/
inline void Frame::box(double swx,double swy, double nex, double ney, int color){
  box(x2i(swx),y2j(swy),x2i(nex),y2j(ney),color);
};

/**
@doc
  Draws a filled box with the botton left corner at (@i(swx), @i(swy)) and
  the right top corner at (@i(nex), @i(ney)). The box is filled with color
  @i(color)
*/
inline void Frame::boxFill(int lti,int ltj,int rbi,int rbj,int col,int pattern){
    RCT r;
#ifndef LINUX
  SetRct(&r,lti,ltj,rbi,rbj);
#else
  SetRct(&r,lti,rbj,rbi,ltj);
#endif
  FillRct(&r,pattern,col);
};

/**
@doc
  Draws a filled box with the botton left corner at (@i(swx), @i(swy)) and
  the right top corner at (@i(nex), @i(ney)). The box is filled with color
  @i(color)
*/
inline void Frame::boxFill(double swx,double swy, double nex, double ney,int col,int pattern){
    RCT r;
#ifndef LINUX
  SetRct(&r,x2i(swx),y2j(swy),x2i(nex),y2j(ney));
#else
  SetRct(&r,x2i(swx),y2j(ney),x2i(nex),y2j(swy));
#endif
  FillRct(&r,pattern,col);
};

/**
@doc
  Draws an arc of an ellipse bound by the rectangle of world coordinates coordinates
  (@i(swx),@i(swy)) and (@i(nex),@i(ney)). The arc is indicated by the points
  (@i(bx),@i(by)) and (@i(ex),@i(ey)). The arc is drawn in the color i@(color)
*/
inline void Frame::arc(double swx,double swy, double nex, double ney,double bx,double by,double ex,double ey,int color){
  arc(x2i(swx),y2j(swy),x2i(nex),y2j(ney),x2i(bx),y2j(by),x2i(ex),y2j(ey),color);
}

/**
@doc
  Fills and area between an arc and its chord. The arch is an arc
  of an ellipse  bound by the rectangle of world coordinates coordinates
  (@i(swx),@i(swy)) and (@i(nex),@i(ney)). The arc is indicated by the points
  (@i(bx),@i(by)) and (@i(ex),@i(ey)). The arc is drawn in the color i@(color)
*/
inline void Frame::arcFill(double swx,double swy, double nex, double ney,double bx,double by,double ex,double ey,int color,int pattern){
  arcFill(x2i(swx),y2j(swy),x2i(nex),y2j(ney),x2i(bx),y2j(by),x2i(ex),y2j(ey),color,pattern);
}


/**
@doc
  Draws an ellipse  bound by the rectangle of world coordinates coordinates
  (@i(lti),@i(ltj)) and (@i(rbi),@i(rbj)). The ellipse is drawn in the color i@(color)
*/

inline void Frame::ellipse(int lti,int ltj,int rbi,int rbj,int color){
  arc(lti,ltj,rbi,rbj,lti,ltj,lti,ltj,color);
}

/**
@doc
  Draws an ellipse  bound by the rectangle of world coordinates coordinates
  (@i(lti),@i(ltj)) and (@i(rbi),@i(rbj)). The ellipse is filled with the
  pattern i@(pattern) in the color i@(color)
*/

inline void Frame::ellipseFill(int lti,int ltj,int rbi,int rbj,int color,int pattern){
  arcFill(lti,ltj,rbi,rbj,lti,ltj,lti,ltj,color,pattern);
}

/**
@doc
  Draws an ellipse  bound by the rectangle of world coordinates coordinates
  (@i(swx),@i(swy)) and (@i(nex),@i(ney)). The ellipse is drawn in the color i@(color)
*/

inline void Frame::ellipse(double swx,double swy, double nex, double ney,int color){
  arc(swx,swy,nex,ney,swx,swy,swx,swy,color);
}

/**
@doc
  Draws an ellipse  bound by the rectangle of world coordinates coordinates
  (@i(swx),@i(swy)) and (@i(nex),@i(ney)). The ellipse is drawn in the color i@(color)
  pattern i@(pattern) in the color i@(color)
*/

inline void Frame::ellipseFill(double swx,double swy, double nex, double ney,int color,int pattern){
  arcFill(swx,swy,nex,ney,swx,swy,swx,swy,color,pattern);
}

/**
@doc
  The same as operator<< - changes the current position to @i(at)
*/
inline Frame  &Frame::operator>>(const At &at){
  cCol=at.col;
  cRow=at.row;
  return *this;
};

/**
@doc
  The same as operator<< - changes the foreground color to @i(c)
*/
inline Frame  &Frame::operator>>(const FgColor &c){
  SetFgColor(c.color);
  return *this;
};

/**
@doc
  The same as operator<< - changes the background color to @i(c)
*/
inline Frame  &Frame::operator>>(const BgColor &c){
  SetBgColor(c.color);
  return *this;
};

/**
@doc
  Checks if the pixel @i(pxl) (in device coordinates) is inside the frame
*/
inline int Frame::isInside(PXL &p){
   return ( p.i >= lti && p.i < rbi && p.j >= ltj && p.j< rbj );
};

}
}

/// @}
