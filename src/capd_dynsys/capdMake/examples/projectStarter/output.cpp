//////////////////////////////////////////////////////////////////////////////
///
///  @file output.cpp
///  
///  @author kapela  @date   Sep 2, 2011
//////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2011 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#include "output.h"
#include <iostream>
#include <iomanip>

void print(const char * name, const capd::Interval & x){
  std::cout.precision(16);
  std::cout << name << " = " << x << std::endl;
}
