/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file usermove.cpp
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#include "capd/krak/usermove.h"

static capd::krak::UserMove suspendedUserMove = capd::krak::UserMove();

capd::krak::UserMove::UserMove(void)
{
   key=NO_KEY;
}


namespace capd{
namespace krak{
/**
  @doc
  Waits for user action and retuns it in @i(um)
*/
void WaitUserMove(capd::krak::UserMove& um)
{
   while(NO_KEY==capd::krak::GetUserMove(um));
}

/**
@doc
  Makes the rectangle @i(r) blink with the prescribed
  frequency and the prescribed colors until a user
  action returned in @i(um)
*/

void WaitUserMove(capd::krak::UserMove& um, capd::krak::Rct &r, int bgColor, int fgColor, double freq)
{
   double last_clock=capd::krak::Clock(),new_clock;
   int fifo=0;
   while(NO_KEY==capd::krak::GetUserMove(um))
   {
      if(capd::krak::Clock()-last_clock > freq)
      {
         new_clock = capd::krak::Clock();
         fifo=1-fifo;
         last_clock = new_clock;
         if(fifo) capd::krak::FillRct(&r,SOLID_P,fgColor);
         else capd::krak::FillRct(&r,SOLID_P,bgColor);
      }
   }
   capd::krak::FillRct(&r,SOLID_P,bgColor);
}

/*
  internal
*/

void SetUserMove(capd::krak::UserMove &um)
{
   suspendedUserMove=um;
}

/**
@doc
  Waits for user action and retuns it in @i(um)
*/

int GetUserMove(capd::krak::UserMove &um)
{
   static int i=0;
   int l=0;
   if(!(++i%5)) l=capd::krak::Button();


   if(suspendedUserMove.key!=NO_KEY)
   {
      um=suspendedUserMove;
   } else {
      um.key=capd::krak::GetKey();
      if(l && um.key==NO_KEY)
      {
         double t=capd::krak::Clock();
         um.key=DragKey;
         do{
            if(!capd::krak::Button())
            {
               um.key=BUTTON_KEY;
               break;
            }
         }while(capd::krak::Clock()-t <= 0.3);
         capd::krak::GetMouse(&um.pxl);
      }
   }
   return um.key;
}
}} // the end of the namespace capd::krak

/// @}
