// Copyright (C) 2004 by William D Kalies. All rights reserved.
//
//-----------------------------------------------------------------------------
// chom.hpp:
//-----------------------------------------------------------------------------

#ifndef _CAPD_CHOM_CHOM_HPP_ 
#define _CAPD_CHOM_CHOM_HPP_ 

#include <new>
#include <list>
#include <utility>
#include <iterator>
#include <algorithm>
#include <functional>
#include <fstream>
#include <stack>

#include <cstdio>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <time.h>
#include <sstream>
#include <string>
#include <iostream>

#include "capd/chom/dim.hpp"

//-----------------------------------------------------------------------------
// NAMING CONVENTIONS:
//   #define macros: all caps and underscore _ between words
//   Types and variables: no caps and underscore _ between words
//   Functions: Capitalize first letter of each word and no underscores
//-----------------------------------------------------------------------------

using namespace std;

extern int periodic; // 0=off, 1=first DIM-1 variables, 2=all DIM variables
extern int cube_bits;
extern int gen_flag[MAX_CHOM_DIM+1];
extern int Power2(int);
extern int GEN_TOL;

#endif // _CAPD_CHOM_CHOM_HPP_ 
