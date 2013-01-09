/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file kernel.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_KERNEL_H_ 
#define _CAPD_KRAK_KERNEL_H_ 
#include "capd/krak/hardware.h"
#include "capd/krak/color.h"
#include "capd/krak/pattern.h"
#include "capd/krak/keys.h"
//#include "capd/capd/myC.h"

/* structure definitions */

namespace capd{
namespace krak{
struct Rct
{
   int ltj,lti,rbj,rbi;
};

struct Pxl
{
   int j,i;
};
}} // the end of the namespace capd::krak

/* hardware dependant primitives */

namespace capd{
namespace krak{

   void OpenGraphics(int hrs,int vrs,int bgcol,int fgcol,int ltx, int lty);
   void CloseGraphics(void);
#if !defined(IBM_CH) && !defined(VIRT_MON) && !defined(SUN_CH)
   void SetBgCol(int col);
   void SetFgCol(int col);
#endif
   void MWLineTo(int i,int j);
   void MoveTo(int i,int j);
   void PlotDot(int i,int j);
   void Crcl(int i,int j,int r);
   void DrawStrng(const char *txt);
   void FillRct(capd::krak::Rct *r,int pattNr,int colNr);
#if defined (WIN95) || defined (WXWIN)
   void FillChord(int ltj, int lti, int rbj, int rbi,
      int bj, int bi, int ej, int ei, int pattNr, int colNr);
   void Arc(int ltj, int lti, int rbj, int rbi, int bj, int bi, int ej, int ei, int colNr);
   void FillRgn(int *r, int lPoints, int pattNr, int colNr);
#endif
   void GetMouse(capd::krak::Pxl *pxl);
   int Button(void);
   double Clock(void);
   long tickClock(void);
   double RClock(void);
   double tck2sec(long);
   void Beep(int freq,int time);
   char *datetime(void);
   int GetKey(void);

#if defined (WIN95) || defined (WXWIN)
   void SetTextSize(int);
   int GetTextSize(void);
#endif
}}
#endif // _CAPD_KRAK_KERNEL_H_ 

/// @}
