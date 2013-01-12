/// @addtogroup setarth
/// @{

/////////////////////////////////////////////////////////////////////////////
/// @file setarth.h
///
/// @author The CAPD Group
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2005 by the CAPD Group.
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details. 

#ifndef _CAPD_TESTS_SETARTH_SETARTH_H_ 
#define _CAPD_TESTS_SETARTH_SETARTH_H_ 
  #define CHANGEPAR "A:View current problem"
  #define ADD       "B:Add current to list"
  #define SELECT    "C:Copy from list"
  #define MAKETEST  "D:Perform test"
  #define SORT      "E:Sort list"
  #define SAVE      "F:Save list"
  #define QUIT      "G:Quit"
  #define ERROR     "H:Error"
#endif // _CAPD_TESTS_SETARTH_SETARTH_H_ 

void makeTest(void);

/******************************************************************************/

struct problemData{
  frstring dynSysName;
  frstring testType;
  double initialSize;
  IVector initialVector;
  IVector initialBox;
  double step;
  int blowuplimit;
  double blowuptime;
  double iteratetime;
  double expansion;
  double max_expansion;
  double min_loc_expansion;
  double max_loc_expansion;
  double min_z,max_z;
};

/// @}
