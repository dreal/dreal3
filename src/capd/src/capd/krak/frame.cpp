/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file frame.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// Documentation added by Mikolaj Zalewski, June 2000.

#include "capd/krak/frame.h"
#include "capd/capd/minmax.h"
namespace capd{
namespace krak{
   Frame rootFrame;
}}

/*
  auxiliary
*/

void capd::krak::Frame::initFrm(int arglti,int argltj,int argrbi, int argrbj, int bgc, int fgc, int im, int jm)
{
   ci = lti = arglti;
   cj = ltj = argltj;
   rbi = argrbi;
   rbj = argrbj;
   imarg = im;
   jmarg = jm;
   cRow = cCol = 0;
   lRow = (rbj - ltj-jm-jm)/capd::krak::fontHght-1;
   lCol = (rbi - lti-im-im)/capd::krak::fontWdth-1;
   cFrm = this;
   capd::krak::dscrFrm(this,0.0,0.0,1.0,1.0);
   bgColor = bgc;
   fgColor = fgc;
   prec = 6;
}

/**
@doc
  Moves the left top corner to (@i(arglti), @i(argltj)) and the left botton
  corner to (@i(argrbi), @i(argrbj)) where the coordinates are given in
  percentage. This function in used internally by some constructors
*/
void capd::krak::Frame::Locate(capd::krak::Frame &prntFrm,int arglti,int argltj,int argrbi,int argrbj)
{
   if (&prntFrm == NULL)
      capd::krak::errorExit("Parent not defined!");
   lti = capd::krak::linear(arglti,(int)0,prntFrm.lti,(int)100,prntFrm.rbi);
   ltj = capd::krak::linear(argltj,(int)0,prntFrm.ltj,(int)100,prntFrm.rbj);
   rbi = capd::krak::linear(argrbi,(int)0,prntFrm.lti,(int)100,prntFrm.rbi);
   rbj = capd::krak::linear(argrbj,(int)0,prntFrm.ltj,(int)100,prntFrm.rbj);
   initFrm(lti,ltj,rbi,rbj);
}

/**
@doc
  Moves the left top corner to @i(lt) and the left botton
  corner to @i(rb) where the coordinates are given in
  text cells. This function in used internally by some constructors
*/
void capd::krak::Frame::Locate(capd::krak::Frame &prntFrm, capd::krak::At &lt, capd::krak::At &rb)
{
   if (&prntFrm == NULL)
      capd::krak::errorExit("Parent not defined!");
   lti=prntFrm.lti + lt.col*capd::krak::fontWdth;
   ltj=prntFrm.ltj + lt.row*capd::krak::fontHght;
   rbi=prntFrm.lti + (rb.col+1)*capd::krak::fontWdth;
   rbj=prntFrm.ltj + (rb.row+1)*capd::krak::fontHght;
   initFrm(lti,ltj,rbi,rbj);
}

/**
@doc
  Generates a new frame as a subframe of @i(prntFrm)
  with left top corner (@i(lti),@i(ltj)),right bottom corner at (@i(rbi),@i(rbj)),
  where the coordinates are given in percentage
  of the horizontal and vertical size of the parent frame
  @param bgc Background color
  @param jgc Foreground color
  @param im,jm Margins
*/
capd::krak::Frame::Frame(capd::krak::Frame &prntFrm,
   int arglti,int argltj,int argrbi,int argrbj,int bgc,int fgc, int im, int jm)
{
   if (&prntFrm == NULL)
      capd::krak::errorExit("Parent not defined!");
   initFrm(
      capd::krak::linear(arglti,(int)0,prntFrm.lti,(int)100,prntFrm.rbi),
      capd::krak::linear(argltj,(int)0,prntFrm.ltj,(int)100,prntFrm.rbj),
      capd::krak::linear(argrbi,(int)0,prntFrm.lti,(int)100,prntFrm.rbi),
      capd::krak::linear(argrbj,(int)0,prntFrm.ltj,(int)100,prntFrm.rbj),
      bgc,fgc,im,jm);
}

/**
@doc
  Generates a new frame as a subframe of @i(prntFrm)
  with left top corner @i(lt), right bottom corner at @i(rb),
  where the coordinates are given in columns and rows of
  the parent frame
  @param bgc Background color
  @param jgc Foreground color
  @param im,jm Margins
*/
capd::krak::Frame::Frame(const capd::krak::Frame &prntFrm,const capd::krak::At &lt,
   const capd::krak::At &rb,int bgc,int fgc, int im, int jm)
{

   if (&prntFrm == NULL)
      capd::krak::errorExit("Parent not defined!");
   initFrm(
      prntFrm.lti + lt.col*capd::krak::fontWdth,
      prntFrm.ltj + lt.row*capd::krak::fontHght,
      prntFrm.lti + (rb.col+1)*capd::krak::fontWdth,
      prntFrm.ltj + (rb.row+1)*capd::krak::fontHght,
      bgc,fgc,im,jm
   );
}

/**
@doc
  It generates a new frame as a subframe of rootFrame
  with left top corner (@i(lti),@i(ltj)), right bottom corner at
  (@i(rbi),@i(rbj)). @i(bgc) and @i(fgc) are the background and foreground color,
  @i(im) and @i(jm) are the margins.
*/
capd::krak::Frame::Frame(int arglti,int argltj,int argrbi,int argrbj,int bgc,int fgc, int im, int jm)
{
   initFrm(arglti,argltj,argrbi,argrbj,bgc,fgc,im,jm);
}

/**
@doc
  Generates a new frame as a subframe of rootFrm
  with left top corner at the top left corner of
  rootFrm, right bottom corner at the botton right
  bottom cornet of rootFrm, and black and white colors
*/
capd::krak::Frame::Frame(void)
{
   initFrm(
      capd::krak::rootFrame.lti,
      capd::krak::rootFrame.ltj,
      capd::krak::rootFrame.rbi,
      capd::krak::rootFrame.rbj,
      WHITE,BLACK
   );
}

/**
@doc
  Generates a new frame as a subframe of @i(prntFrm) and sets the world
  coordinates and colors
@param lti,ltj The coordinates of the left top corner in percentage of the
   parent frame
@param rbi,rbj The coordinates of the right botton corner in percentage of
   the parent frame
@param swx,swy,nex,ney The world coordinates. Check setWorldCoord for details
@param bgc,fgc The background and foreground color
@param im,jm The margins for text in device coordinates
*/
capd::krak::Frame::Frame(capd::krak::Frame &prntFrm,int the_lti,int the_ltj,int the_rbi,int the_rbj,
             double the_swx,double the_swy,double the_nex,double the_ney,
             int the_bgc,int the_fgc, int the_im, int the_jm)
{
   Locate(prntFrm,the_lti,the_ltj,the_rbi,the_rbj);
   imarg=the_im;
   jmarg=the_jm;
   cRow= cCol=0;
   lRow= (rbj - ltj-jmarg-jmarg)/capd::krak::fontHght-1;
   lCol= (rbi - lti-imarg-imarg)/capd::krak::fontWdth-1;
   cFrm=this;
   bgColor=the_bgc;
   fgColor=the_fgc;
   dscrFrm(this,the_swx,the_swy,the_nex,the_ney);
}

/**
@doc
  draws a line from the current position to (@i(i), @i(j))
  using the color @i(color). If color is FRAME_FG then the
  frame foreground color is used.
*/
void capd::krak::Frame::draw(int i,int j,int color)
{
   int c=c_fgcol;
   if(color == FRAME_FG) color=fgColor;
   capd::krak::SetFgCol(color);
   capd::krak::MoveTo(ci,cj);
   capd::krak::LineTo(i,j);
   jump(i,j);
   capd::krak::SetFgCol(c);
}

/**
@doc
  draws the text given by @i(t) from the current position
  using the color @i(color). If color is FRAME_FG then the
  frame foreground color is used.
*/
void capd::krak::Frame::drawText(const char *t, int i,int j,int color)
{
   int c=c_fgcol;
   int b=c_bgcol;
   if(color == FRAME_FG) color=fgColor;
   capd::krak::SetFgCol(color);
   capd::krak::SetBgCol(bgColor);
   capd::krak::MoveTo(i,j);
   capd::krak::DrawStrng(t);
   capd::krak::SetFgCol(c);
   capd::krak::SetBgCol(b);
}

/**
@doc
  Draw a dot at position (@i(i), @i(j)) (in pixel coordinates)
  and color @i(color)
*/
void capd::krak::Frame::dot(int i,int j,int color)
{
   cFrm=this;
   int c_col=c_fgcol;
   if(color == FRAME_FG) color=fgColor;
   capd::krak::SetFgCol(color);
   capd::krak::PlotDot(i, j);
   capd::krak::SetFgCol(c_col);
}

/**
@doc
  Draw a dot at position (@i(x), @i(y)) (in world coordinates)
  and color @i(color)
*/
void capd::krak::Frame::dot(double x,double y,int color)
{
   cFrm=this;
   int c_col=c_fgcol;
   if(color == FRAME_FG) color=fgColor;
   capd::krak::SetFgCol(color);
   capd::krak::PlotDot(x2i(x),y2j(y));
   capd::krak::SetFgCol(c_col);
}

/**
@doc
  Draw a circle at position (@i(i), @i(j)) of radius @i(r) (in pixel coordinates)
  and color @i(color)
*/
void capd::krak::Frame::circle(int i,int j,int r, int color)
{
   cFrm=this;
   int c_col=c_fgcol;
   if(color == FRAME_FG) color=fgColor;
   capd::krak::SetFgCol(color);
   capd::krak::Crcl(i,j,r);
   capd::krak::SetFgCol(c_col);
}

/**
@doc
  Draw a circle at position (@i(x), @i(y)) (in world coordinates)
  of radius @i(r) (in pixel coordinates) and color @i(color)
*/
void capd::krak::Frame::circle(double x,double y,int r, int color)
{
   cFrm=this;
   int c_col=c_fgcol;
   if(color == FRAME_FG) color=fgColor;
   capd::krak::SetFgCol(color);
   capd::krak::Crcl(x2i(x),y2j(y),r);
   capd::krak::SetFgCol(c_col);
}

/**
@doc
  Draws a line from the point (@i(x1), @i(y1)) to (@i(x2), @i(y2)) (in pixel
  coordinates)in the color @i(color). The current position is moved to the
  end of the line
*/
void capd::krak::Frame::line(int x1, int y1, int x2, int y2, int color)
{
   jump(x1, y1);
   draw(x2, y2, color);
}

/**
@doc
  Draws a line from the point (@i(x1), @i(y1)) to (@i(x2), @i(y2)) (in world
  coordinates)in the color @i(color). The current position is moved to the
  end of the line
*/
void capd::krak::Frame::line(double x1, double y1, double x2, double y2, int color)
{
   jump(x1, y1);
   draw(x2, y2, color);
}

#if defined (WIN95) || defined (WXWIN)
/**
@doc
  Draws a polygon given by @i(nPoints) pairs of the coordinates
  in the table @i(coords) in the color i@(color)
*/
void capd::krak::Frame::polygon(int coords[],int nPoints,int color)
{
   jump(coords[0],coords[1]);
   for(int i=2;i<2*nPoints;i+=2)
      draw(coords[i],coords[i+1],color);
}

/**
@doc
  Draws a polygon given by @i(nPoints) pairs of the world coordinates
  in the table @i(coords) in the color i@(color)
*/
void capd::krak::Frame::polygon(double coords[],int nPoints,int color)
{
   jump(coords[0],coords[1]);
   for(int i=2;i<2*nPoints;i+=2)
      draw(coords[i],coords[i+1],color);
}
/**
@doc
  Fills a polygon given by @i(nPoints) pairs of the coordinates
  in the table @i(coords) in the color i@(color)
*/
void capd::krak::Frame::polygonFill(int coords[],int nPoints,int col,int pattern)
{
   capd::krak::FillRgn(coords,nPoints,pattern,col);
}


/**
@doc
  Fills a polygon given by @i(nPoints) pairs of the world coordinates
  in the table @i(coords) in the color i@(color)
*/
void capd::krak::Frame::polygonFill(double coords[],int nPoints,int color,int pattern)
{
   int* icoords=new int[2*nPoints];
   for(int i=0;i<nPoints;i++)
   {
      icoords[i+i]=x2i(coords[i+i]);
      icoords[i+i+1]=y2j(coords[i+i+1]);
   }
   polygonFill(icoords,nPoints,color,pattern);
}

/**
@doc
  Draws an arc of an ellipse bound by the rectangle of coordinates
  (@i(lti),@i(ltj)) and (@i(rbi),@i(rbj)). The arc is indicated by the points
  (@i(bi),@i(bj)) and (@i(ei),@i(ej)). The arc is drawn in the color i@(color)
*/
void capd::krak::Frame::arc(int lti,int ltj,int rbi,int rbj,int bi,int bj,int ei,int ej,int color)
{
   capd::krak::Arc(lti,ltj,rbi,rbj,bi,bj,ei,ej,color);
}

/**
@doc
  Fills and area between an arc and its chord. The arch is an arc
  of an ellipse bound by the rectangle of coordinates
  (@i(lti),@i(ltj)) and (@i(rbi),@i(rbj)). The arc is indicated by the points
  (@i(bi),@i(bj)) and (@i(ei),@i(ej)). The arc is drawn in the color i@(color)
*/
void capd::krak::Frame::arcFill(int lti,int ltj,int rbi,int rbj,int bi,int bj,int ei,int ej,int col,int pattern)
{
   capd::krak::FillChord(lti,ltj,rbi,rbj,bi,bj,ei,ej,pattern,col);
}
#endif

/**
@doc
  Draw a cross at position (@i(x), @i(y)) (in world coordinates),
  color @i(color) and size @i(size)
*/
void capd::krak::Frame::Xcrss(double x,double y,int size,int color)
{
   cFrm=this;
   int c_col=c_fgcol;
   if(color == FRAME_FG) color=fgColor;
   capd::krak::SetFgCol(color);
   capd::krak::Xcross(x2i(x),y2j(y),size);
   capd::krak::SetFgCol(c_col);
}

/**
@doc
  Print a color text on the frame. The current color isn't changed by that
  function
*/
capd::krak::Frame &capd::krak::Frame::operator<<(const capd::krak::colstring &a_colstring)
{
   int save_c_bgcol=c_bgcol,save_c_fgcol=c_fgcol;
   capd::krak::SetFgCol(a_colstring.fgcolor);
   capd::krak::SetBgCol(a_colstring.bgcolor);
   capd::krak::DrawTxtg(this,a_colstring.string());
   capd::krak::SetFgCol(save_c_fgcol);
   capd::krak::SetBgCol(save_c_bgcol);
   return *this;
}

/**
@doc
  Prints the character @i(c) at the current position
*/
capd::krak::Frame &capd::krak::Frame::operator<<(char c)
{
   char buf[2];
   buf[0]=c; buf[1]=0;
   capd::krak::DrawTxtg(this,buf);
   return *this;
}

/**
@doc
  Prints the number @i(n) at the current position
*/
capd::krak::Frame &capd::krak::Frame::operator<<(long n)
{
   std::ostringstream bufstream;
   bufstream << n << '\0';
   capd::krak::DrawTxtc(this,(char *)(bufstream.str().c_str()));
   return *this;
}

/**
@doc
  Prints the number @i(n) at the current position
*/
capd::krak::Frame &capd::krak::Frame::operator<<(int n)
{
   std::ostringstream bufstream;
   bufstream << n << '\0';
   capd::krak::DrawTxtc(this,(char *)(bufstream.str().c_str()));
   return *this;
}

/**
@doc
  Outputs the double @i(r), eg.:
<pre>
frm<<3.14159;
</pre>
*/
capd::krak::Frame &capd::krak::Frame::operator<<(double r)
{
   std::ostringstream bufstream;
   bufstream.precision(prec);
   bufstream << r << '\0';
   capd::krak::DrawTxtc(this,(char *)(bufstream.str().c_str()));
   return *this;
}

/**
@doc
  Outputs the string @i(a_string) on the frame.
*/
capd::krak::Frame &capd::krak::Frame::operator<<(const capd::krak::frstring &a_string)
{
   capd::krak::frstring t=a_string;
   capd::krak::DrawTxtc(this,t.string());
   return *this;
}

/**
@doc
  Outputs the string @i(text) on the frame.
*/
capd::krak::Frame &capd::krak::Frame::operator<<(char *text)
{
   capd::krak::DrawTxtc(this,text);
   return *this;
}


namespace capd{
namespace krak{
/**
@doc
  Read a string from the keybord. See also Edit().
*/
void getText(capd::krak::Frame &frm, capd::krak::frstring &text)
{
   int i,txtpos=0;
   int ch;
   char buf[256];
   int Row=frm.cRow,Col=frm.cCol;

   do{
      frm << "_";
      ch=inchar();
      frm << capd::krak::At(Row,Col);
      for (i=0;i<=txtpos;i++) frm << " ";
      if (ch == '\b' )
      {
         if (txtpos>0) --txtpos;
      } else {
         *(buf + txtpos++)=ch;
      }
      frm << capd::krak::At(Row,Col);
      for (i=0;i<txtpos;i++) frm << *(buf+i);
   }while (!(ch =='\n' || ch =='\r' || txtpos>=254));

   frm << capd::krak::At(Row,Col+txtpos) << " ";
   *(buf+txtpos)='\0';
   text = capd::krak::frstring(buf);
}
}}

/**
@doc
  Reads a string from the keyboard. The same, as getText.
*/
capd::krak::Frame &capd::krak::Frame::operator>>(capd::krak::frstring &a_string)
{
   capd::krak::getText(*this,a_string);
   return *this;
}

/**
@doc
  Reads a number from the keyboard using getText().
*/
capd::krak::Frame &capd::krak::Frame::operator>>(int &n)
{
   capd::krak::frstring in_string;
   capd::krak::getText(*this,in_string);
   std::istringstream bufstream(in_string.string());
   bufstream >> n;
   return *this;
}

/**
@doc
  Reads a number from the keyboard using getText().
*/
capd::krak::Frame &capd::krak::Frame::operator>>(long &n)
{
   capd::krak::frstring in_string;
   capd::krak::getText(*this,in_string);
   std::istringstream bufstream(in_string.string());
   bufstream >> n;
   return *this;
}

/**
@doc
  Reads a double from the keyboard using getText().
*/

capd::krak::Frame &capd::krak::Frame::operator>>(double &r)
{
   capd::krak::frstring in_string;
   capd::krak::getText(*this,in_string);
   std::istringstream bufstream(in_string.string());
   bufstream >> r;
   return *this;
}

/**
@doc
  A more sophisticated version of getText. Reads a text from the keybord and
  allows the user to use arrows backspace and delete. Returns the key used to
  end the edition (eg. Enter, Escape)
@param at The position of the begining of the edition
@param no_col The number of columns used for the edition
@param s The string. Then calling it contains the text that should appear
  in the edition. The result string in also returned here.
*/
int capd::krak::Frame::Edit(capd::krak::At at, int no_col, capd::krak::frstring &s)
{
   capd::krak::flexstring visible;
   int i,firstseen=0,lastseen=no_col-1,cursor_pos=0,finish=0;
   int length=strlen(s.string())-1; // strlen counts the terminating zero!
   int key=NO_KEY,col=at.col,row=at.row;
   char c;

   capd::krak::SetFgCol(BLACK);
   capd::krak::SetBgCol(WHITE);
   *this << at;
   for(i=firstseen;i<=lastseen;i++) *this << " ";

   do{
// this is intended for speeding up
      visible=s(firstseen,min(lastseen,length-1));
      if(length<lastseen) visible=visible^" ";
      if(length-1<lastseen) visible=visible^" ";
      *this << at;
      capd::krak::SetFgCol(BLACK);
      capd::krak::SetBgCol(WHITE);
      capd::krak::DrawTxtg(this,visible.string());
      c=(cursor_pos<length?s.character(cursor_pos):' ');
      capd::krak::SetFgCol(WHITE);
      capd::krak::SetBgCol(BLACK);
      *this << At(row,col+cursor_pos-firstseen) << c;
      capd::krak::SetFgCol(BLACK);
      capd::krak::SetBgCol(WHITE);

      while(!capd::krak::Button() && NO_KEY==(key=capd::krak::GetKey()));
      if(key>=32 && key<128)
      {
         s.insert(cursor_pos,(char)key);cursor_pos++;length++;
      } else {
         switch(key)
         {
            case LeftKey:  if(cursor_pos>0) cursor_pos--;break;
            case RightKey: if(cursor_pos<length) cursor_pos++;break;
            case BSKey:
               if(cursor_pos>0){
                  cursor_pos--;s.remove(cursor_pos);length--;
                  *this << capd::krak::At(row,col+length-firstseen) << ' ';
               }
               break;
            case DelKey:
               if(cursor_pos<length){
                  s.remove(cursor_pos);length--;
                  *this << capd::krak::At(row,col+length-firstseen) << ' ';
               }
               break;
            default:  finish=1;
         }
      }

      if(cursor_pos<firstseen)
      {
         firstseen=cursor_pos;
         lastseen=firstseen+no_col-1;
      }
      if(cursor_pos>lastseen)
      {
         lastseen=cursor_pos;
         firstseen=lastseen-no_col+1;
      }
//rootFrame << At(4,0) << (char)key << " " << key << ' ' << LeftKey << ' ' <<
//      finish << ' ' << frstrlen(s) << "   ";
   }while(!finish);
   return key;
}

namespace capd{
namespace krak{
void pause(int i,int j, capd::krak::frstring s)
{
   capd::krak::rootFrame << capd::krak::At(i,j) << s << "    ";
   capd::krak::waitBt();
}
}}

/// @}
