/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file ms-win31.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

// krak/krak.h include for WIN 3.1
#  ifdef _low_level_
#    include <windows.h>
#  endif
#    define IBM
#  ifdef LAPTOP
#    define F_HGHT 14
#    define F_WDTH 7
#  else
#    define F_HGHT 14
#    define F_WDTH  7
#  endif
#  define MAX_COLOR_NO 16
#  ifndef COLOR256
#    define MAX_PALETTE 16
#    define RAINBOW(x) gray[min(15,max(2,(int)(2+(1.-x)*14)))]
#  else
#    define MAX_PALETTE 216
#    define RAINBOW(x) min(215,max(16,(int)(16+(1.-x)*200)))
#  endif
#  define main mainEntry
#  define LineTo(i,j) MWLineTo(i,j)
   void EmptyMQueue(void);
#  ifdef _low_level_
   int PASCAL WinMain (HINSTANCE hI, HINSTANCE hPI,LPSTR lpszCmd, int nCS);
   long FAR PASCAL _export WndProc (HWND hwnd, WORD message, WORD wParam, LONG lParam);
   int mainEntry(int argc, char *argv[]);

   extern HDC hdc;
#  endif
#  define SYSTEM "IBM MS Windows (GR)"

#  define TAB_KEY 9

/// @}
