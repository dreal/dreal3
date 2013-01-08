//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file divtst.cpp
///
///
/// @author kapela  @date 2010-02-23
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) CAPD group 
//
// This file constitutes a part of the CAPD library, 
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details. 

#include <iostream>
#include "capd/interval/DoubleInterval.h"
int main ()
{
    interval x3 = interval(1.0, 1.0) / 3.0;
    if (x3. leftBound () != x3. rightBound ())
        std::cout << "Result seems to be OK\n";
    else
        std::cout << "Incorrect result in division (1.0,1.0)/3.0\n";
    return 0;
}


