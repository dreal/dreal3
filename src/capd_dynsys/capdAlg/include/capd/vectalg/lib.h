//////////////////////////////////////////////////////////////////////////////
//   Package:          CAPD

/////////////////////////////////////////////////////////////////////////////
//
/// @file vectalg/lib.h
///
/// @author Tomasz Kapela   @date 2010-01-23
//
/////////////////////////////////////////////////////////////////////////////

// Copyright (C) Tomasz Kapela 2010
//
// This file constitutes a part of the CAPD library,
// distributed under the terms of the GNU General Public License.
// Consult  http://capd.ii.uj.edu.pl/ for details.

#ifndef _CAPD_VECTALG_LIB_H_
#define _CAPD_VECTALG_LIB_H_

double power(int val,int ile);

#include "capd/intervals/lib.h"

#include "capd/vectalg/Dimension.h"
#include "capd/vectalg/Vector.h"
#include "capd/vectalg/Matrix.h"
#include "capd/vectalg/Norm.h"
#include "capd/matrixAlgorithms/floatMatrixAlgorithms.h"
#include "capd/matrixAlgorithms/intMatrixAlgorithms.hpp"
#include "capd/vectalg/Multiindex.h"

#define CAPD_USER_NAMESPACE capd
  #include "capd/vectalg/typedefs.h"
#undef CAPD_USER_NAMESPACE

#endif // _CAPD_VECTALG_LIB_H_
