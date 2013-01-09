/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file manip.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_MANIP_H_ 
#define _CAPD_KRAK_MANIP_H_ 

namespace capd{
namespace krak{
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

}} // the end of the namespace capd::krak

// ###############################  inline definitions ########################

inline capd::krak::At::At(int r,int c)
{
   row=r;col=c;
}

inline capd::krak::Tab::Tab(int c)
{
   col=c;
}

inline capd::krak::FgColor::FgColor(int c)
{
   color=c;
}

inline capd::krak::BgColor::BgColor(int c)
{
   color=c;
}

#endif // _CAPD_KRAK_MANIP_H_ 

/// @}
