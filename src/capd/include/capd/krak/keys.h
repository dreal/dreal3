/// @addtogroup krak
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file keys.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_KRAK_KEYS_H_ 
#define _CAPD_KRAK_KEYS_H_ 

#define NO_KEY 0x1ff
#define DRAG_KEY 0x1fd
#define BUTTON_KEY 0x1fe

#if defined (WXWIN)
   enum FunctKeys{BSKey=8,TabKey,CRKey=13,PgUpKey=312,PgDnKey,EndKey,HomeKey,
                  LeftKey,UpKey,RightKey,DownKey,
                  InsKey=324,DelKey=127,EscKey=27,
                  F1Key=342,F2Key,F3Key,F4Key,F5Key,F6Key,F7Key,F8Key,F9Key,
                  DragKey=DRAG_KEY,ButtonKey=BUTTON_KEY,NoKey=NO_KEY};
#elif defined (IBM)
   enum FunctKeys{BSKey=8,TabKey,CRKey=13,PgUpKey,PgDnKey,EndKey,HomeKey,
                  LeftKey,UpKey,RightKey,DownKey,
                  InsKey,DelKey,EscKey=27,
                  F1Key=89,F2Key,F3Key,F4Key,F5Key,F6Key,F7Key,F8Key,F9Key,
                  DragKey=DRAG_KEY,ButtonKey=BUTTON_KEY,NoKey=NO_KEY};

#else
   enum FunctKeys{BSKey=65288,TabKey,CRKey=65293,PgUpKey=65365,PgDnKey,EndKey,HomeKey=65360,
                  LeftKey,UpKey,RightKey,DownKey,
                  InsKey=65379,DelKey=65535,EscKey=65307,
                  F1Key=65386,F2Key=65488,F3Key=65489,F4Key=65485,F5Key=65487,F6Key=65475,F7Key,F8Key,F9Key,
                  DragKey=DRAG_KEY,ButtonKey=BUTTON_KEY,NoKey=NO_KEY};
#endif

#endif // _CAPD_KRAK_KEYS_H_ 

/// @}
