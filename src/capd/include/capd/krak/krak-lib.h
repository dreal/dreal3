/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file krak-lib.h
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
   in a simplified verion for educational purposes
   Author: Marian Mrozek
*/

namespace capd{
/// Krak - a basic portable graphic library
namespace krak{

/* structure definitions */

class Frame;
typedef class Frame FRAME;
/* Externals */

extern int fontHght,fontWdth;
extern Frame rootFrame;
extern FRAME *rootFrm;

#define gout rootFrame
#define main() mainEntry(int,char**)



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

/* primitive class Frame */

class Frame{
  public:

  int ltj,lti,rbj,rbi,cj,ci;
  int imarg,jmarg;
  double swx,swy,nex,ney;
  int cRow,cCol,lRow,lCol;
  int bgColor,fgColor;
  int prec;

  Frame(void);

  Frame &operator<<(char c);
  Frame &operator<<(int n);
  Frame &operator<<(long n);
  Frame &operator<<(double r);

  Frame &operator<<(char *text);

  Frame &operator<<(const FgColor &c);
  Frame &operator<<(const BgColor &c);
  friend Frame &operator<<(Frame &f,const  At &at);
  Frame &operator<<(const Tab tab);


  Frame &operator>>(const At &at);
  Frame &operator>>(const FgColor &c);
  Frame &operator>>(const BgColor &c);

  Frame &operator>>(int &n);
  Frame &operator>>(long &n);
  Frame &operator>>(double &r);

  void SetBgColor(int c);
  void SetFgColor(int c);

};

// ###############################  inline definitions ########################

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
inline Frame &Frame::operator<<(const Tab tab){
  cCol=tab.col;
  return *this;
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

int Button(void);

inline int  button(void){
  return Button();
};

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

double Clock(void);
void delay(double t);

#define NO_KEY 0x1ff
#define DRAG_KEY 0x1fd
#define BUTTON_KEY 0x1fe

enum FunctKeys{BSKey=8,TabKey,CRKey=13,PgUpKey,PgDnKey,EndKey,HomeKey,
    LeftKey,UpKey,RightKey,DownKey,
    InsKey,DelKey,EscKey=27,
          F1Key=89,F2Key,F3Key,F4Key,F5Key,F6Key,F7Key,F8Key,F9Key,
    DragKey=DRAG_KEY,ButtonKey=BUTTON_KEY,NoKey=NO_KEY};


/* Graphic window routines */

void closeGraphics(void);
void openGraphics(int hrs,int vrs,int bgcol,int fgcol,int ltx=100, int lty=100);
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

void keyAndMouse(int& key, double& x,double& y);
void mouse(double x,double y);

/* Basic mouse and keybord routines */

int  button(void);
void waitButton(void);

void setTextSize(int size);
int getTextSize(void);
void setBackgroundColor(int color);
void setForegroundColor(int color);

}// end of namespace krak
}// end of namespace capd

using namespace capd::krak;

/// @}
