
/////////////////////////////////////////////////////////////////////////////
/// @file CRefTest.cpp
///
/// @author Marian Mrozek
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) 2000-2007 by the CAPD Group.
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.wsb-nlu.edu.pl/ for details.

#include <iostream>
#include "capd/auxil/CRef.h"

int main(){
  CRef<int> c(new int());
  c()=7;
  ++c();
  std::cout << c() << " count is " << c.count() << std::endl;
  {
    CRef<int> d=c;
    ++d();
    std::cout << *d << " count is " << c.count() << std::endl;
  }
  std::cout << c() << " count is " << c.count() << std::endl;
}
